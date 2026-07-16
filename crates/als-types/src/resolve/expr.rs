//! The expression type checker (resolution-doc §4): a single bidirectional
//! walk that computes each node's bounding type bottom-up and resolves overload
//! choices top-down against the relevant type pushed from the parent (see the
//! module-level note in `resolve/mod.rs` on the fused-pass structure).
//!
//! No `int`↔`Int` coercion (resolution-doc §4.5): `+ - = != in` are purely
//! relational; only `#`, `sum`/`int`, and the `fun/…` binops produce
//! primitive ints. The candidate scope chain follows §4.4:
//! qualified prefix → local env → builtins → sigs/params → funcs/preds →
//! fields (with implicit-`this` candidates inside a sig context).

use std::collections::BTreeSet;

use als_syntax::ast::{
    BinOp, CmpOp, Const, Decl, DeclId, Expr, ExprId, ExprKind, LetBinding, QualName, Quant, UnOp,
};
use als_syntax::{ArenaId, Span};

use crate::error::ResolveError;
use crate::graph::ModuleId;
use crate::ty::Type;
use crate::warning::ResolveWarning;
use crate::world::{FuncId, SigId};

use super::Resolver;

/// The relevant type pushed down during resolution (resolution-doc §4.3/§4.4).
#[derive(Clone)]
pub(super) enum Want {
    /// No constraint.
    Any,
    /// `resolve_as_formula`: must be boolean.
    Formula,
    /// `resolve_as_set`: any relational value. A **definite** set position
    /// (a `some/no/one/lone/#` operand, a decl bound): a residual overload
    /// ambiguity here is a genuine reject.
    Set,
    /// A set position mettle resolves **leniently** for ambiguity — the operand
    /// of a relational join, whose precise per-column relevant slice mettle only
    /// approximates, so it must never raise an ambiguity reject (`prev.t"` with
    /// two `prev` overloads is disambiguated by the join slice in the reference).
    SetLoose,
    /// `resolve_as_int`: an integer.
    Int,
    /// The right operand of a relational join: prefer candidates whose first
    /// column can join with the given left type (field disambiguation, §4.3).
    JoinRhs(Type),
    /// The left operand of a relational join: prefer candidates whose last
    /// column can join with the given right type (the join-retry, §4.4).
    JoinLhs(Type),
    /// A relevant type a candidate must intersect at a **definite** position
    /// (the `=`/`in` operand slices, where a residual ambiguity is a reject).
    Of(Type),
    /// A relevant type used to **narrow** a candidate, but **leniently**: it
    /// filters the overload but never raises an ambiguity reject (the `+`/`&`/
    /// `-`/`++` right operand and call arguments, whose precise slice mettle
    /// only approximates).
    OfLoose(Type),
}

/// A resolved value candidate for a name (resolution-doc §4.4).
struct Cand {
    ty: Type,
    /// Disambiguation weight: implicit-`this`/cross-branch fields cost more, so
    /// min-weight prefers direct references (resolution-doc §4.4 step 3).
    weight: i32,
}

/// A call candidate: a func/pred usable via box join.
struct CallCand {
    ret: Type,
    params: Vec<Type>,
    reason: String,
}

/// The expression-typing context: an immutable view of the resolved world plus
/// the mutable lexical env and diagnostic sinks. Borrows `&Resolver`
/// immutably, so the caller collects `errors`/`warnings` after the borrow ends.
pub(super) struct Cx<'a, 'g> {
    pub r: &'a Resolver<'g>,
    pub module: ModuleId,
    /// Lexical env (innermost binding last): let/quantifier vars, params, `this`.
    pub env: Vec<(String, Type)>,
    /// The enclosing sig, for implicit-`this` field resolution (`None` at top
    /// level, resolution-doc §3.3).
    pub rootsig: Option<SigId>,
    /// A non-defined field bound: func/pred calls are disallowed (§3.4).
    pub no_calls: bool,
    /// The field label being bound (for the call-in-bound reject message).
    pub field_name: String,
    pub errors: Vec<ResolveError>,
    pub warnings: Vec<ResolveWarning>,
    /// Remaining macro-substitution budget (resolution-doc §3.7, starts at 20).
    unroll: u32,
    /// Set when an overloaded name was resolved accept-lean (>1 surviving
    /// candidate) somewhere in the current top-level formula. Arity rejects are
    /// suppressed while it holds: the wrong-arity type may be an artifact of the
    /// arbitrary choice, not a genuine mismatch. A fully unambiguous formula
    /// (probe 13) keeps it clear, so real arity errors still fire.
    ambig: bool,
    /// Set while resolving a relational join whose operand involved a
    /// multi-candidate joinability pick (mt-022). Suppresses only the enclosing
    /// `IllegalJoin` check — a locally-chosen join reading may be globally wrong,
    /// so an empty outer join might not be a genuine illegal join. Scoped by the
    /// join arm (saved/restored), unlike the formula-wide `ambig`.
    join_lenient: bool,
    /// Env var names referenced so far (for the unused-binder warning).
    used: BTreeSet<String>,
}

impl<'a, 'g> Cx<'a, 'g> {
    pub(super) fn new(r: &'a Resolver<'g>, module: ModuleId) -> Self {
        Cx {
            r,
            module,
            env: Vec::new(),
            rootsig: None,
            no_calls: false,
            field_name: String::new(),
            errors: Vec::new(),
            warnings: Vec::new(),
            unroll: 20,
            ambig: false,
            join_lenient: false,
            used: BTreeSet::new(),
        }
    }

    fn ast(&self) -> &'g als_syntax::ast::Ast {
        self.r.ast(self.module)
    }

    fn expr(&self, e: ExprId) -> &'g Expr {
        &self.ast().exprs[e]
    }

    fn err(&mut self, e: ResolveError) {
        self.errors.push(e);
    }

    // ---- public entry points (the three `resolve_as_*` wrappers, §4.3) ----

    /// `resolve_as_formula`: type-check `e` as a formula.
    pub(super) fn run_formula(&mut self, e: ExprId) {
        self.ambig = false;
        self.check(e, &Want::Formula);
    }

    /// `resolve_as_set`: type-check `e` as a relational value, returning its
    /// set type.
    pub(super) fn run_set(&mut self, e: ExprId) -> Type {
        self.ambig = false;
        let t = self.check(e, &Want::Set);
        t.as_set(self.r.world.builtins.int)
    }

    /// Resolves a declaration bound (field/param/quant), returning the relation
    /// type it denotes (multiplicity markers strip away; `seq` adds the index
    /// column).
    pub(super) fn run_bound(&mut self, e: ExprId) -> Type {
        self.ambig = false;
        let t = self.check(e, &Want::Set);
        t.as_set(self.r.world.builtins.int)
    }

    // ---- the core walk ----

    fn check(&mut self, e: ExprId, want: &Want) -> Type {
        let ty = self.check_kind(e, want);
        let span = self.expr(e).span;
        self.typecheck(&ty, want, span);
        ty
    }

    /// The reference's `typecheck_as_{formula,int,set}` sort check (resolution-doc
    /// §4.3): once a node's bounding type is known, the position it sits in
    /// requires a particular sort. A relational value where a formula is
    /// required (or vice versa), or a non-int where an int is required, is an
    /// `ErrorType` → REJECT.
    ///
    /// Suppressed when the subtree involved an accept-lean overload pick
    /// (`self.ambig`) or already carries an error (`ty.is_error()`), so the
    /// approximation never *wrongly rejects* a real model (ADR-0009): a wrong
    /// sort there may be an artifact of the arbitrary choice, exactly as for the
    /// arity check.
    fn typecheck(&mut self, ty: &Type, want: &Want, span: Span) {
        if self.ambig || ty.is_error() {
            return;
        }
        match want {
            Want::Any => {}
            Want::Formula => {
                if !ty.is_bool {
                    self.err(ResolveError::NotFormula { span });
                }
            }
            Want::Int => {
                if !ty.is_small_int && !ty.is_int(&self.r.world) {
                    self.err(ResolveError::NotInt { span });
                }
            }
            // Every set position (`Set` and the join/comparison disambiguation
            // hints, which are all set positions in the reference) rejects a
            // boolean value used as a relation.
            Want::Set
            | Want::SetLoose
            | Want::Of(_)
            | Want::OfLoose(_)
            | Want::JoinRhs(_)
            | Want::JoinLhs(_) => {
                if ty.is_bool {
                    self.err(ResolveError::NotSet { span });
                }
            }
        }
    }

    fn check_kind(&mut self, e: ExprId, want: &Want) -> Type {
        let node = self.expr(e);
        let span = node.span;
        match &node.kind {
            ExprKind::Num(_) => Type::small_int(self.r.world.builtins.int),
            ExprKind::Str(_) => Type::unary(self.r.world.builtins.string),
            ExprKind::Const(c) => self.const_type(*c),
            ExprKind::This => self.this_type(span),
            ExprKind::Name(qn) => self.resolve_name(qn, want, false),
            ExprKind::AtName(qn) => self.resolve_name(qn, want, true),
            ExprKind::Unary { op, expr } => self.unary(*op, *expr, span, want),
            // Join and box join both resolve via the applicative pass (§4.4).
            ExprKind::Binary {
                op: BinOp::Join, ..
            }
            | ExprKind::BoxJoin { .. } => self.applicative(e, span, want),
            ExprKind::Binary { op, lhs, rhs } => self.binary(*op, *lhs, *rhs, span),
            ExprKind::Arrow { lhs, rhs, .. } => self.arrow(*lhs, *rhs),
            ExprKind::Compare { op, lhs, rhs, .. } => self.compare(*op, *lhs, *rhs, span),
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self.if_then_else(*cond, *then_branch, *else_branch, want),
            ExprKind::Quant { quant, decls, body } => self.quant(*quant, decls, *body, span),
            ExprKind::Comprehension { decls, body } => self.comprehension(decls, *body),
            ExprKind::Let { bindings, body } => self.let_expr(bindings, *body, want),
            ExprKind::Block(exprs) => {
                // A single-element brace group `{ e }` is grouping (parens), so
                // it takes the parent's relevant type and yields `e`'s type — a
                // set `{a + b}` on the right of `in` stays a set, not a formula.
                // A multi-formula block `{ f1 f2 }` is an implicit conjunction.
                if let [only] = exprs.as_slice() {
                    let only = *only;
                    self.check(only, want)
                } else {
                    for &f in exprs {
                        self.check(f, &Want::Formula);
                    }
                    Type::formula()
                }
            }
        }
    }

    fn const_type(&self, c: Const) -> Type {
        match c {
            Const::None => Type::unary(self.r.world.builtins.none),
            Const::Univ => Type::unary(self.r.world.builtins.univ),
            Const::Iden => {
                Type::product_of(vec![self.r.world.builtins.univ, self.r.world.builtins.univ])
            }
        }
    }

    /// A pure bottom-up bounding type for `e` (the reference's `.type` after
    /// `make`), with **no** error/warning emission and **no** choice resolution:
    /// an overloaded name yields the *merge* of its candidate types (as
    /// `ExprChoice.make` does). Used to peek a sibling's type when computing a
    /// child's precise relevant type (`=`/`in` slices, resolution-doc §4.2/§4.3).
    /// Read-only: it clones `env`/`rootsig` state through the recursion.
    fn infer(&self, e: ExprId) -> Type {
        let node = self.expr(e);
        match &node.kind {
            ExprKind::Num(_) => Type::small_int(self.r.world.builtins.int),
            ExprKind::Str(_) => Type::unary(self.r.world.builtins.string),
            ExprKind::Const(c) => self.const_type(*c),
            ExprKind::This => self.infer_this(),
            ExprKind::Name(qn) => self.infer_name(qn, false),
            ExprKind::AtName(qn) => self.infer_name(qn, true),
            ExprKind::Unary { op, expr } => self.infer_unary(*op, *expr),
            ExprKind::Binary {
                op: BinOp::Join, ..
            }
            | ExprKind::BoxJoin { .. } => self.infer_applicative(e),
            ExprKind::Binary { op, lhs, rhs } => self.infer_binary(*op, *lhs, *rhs),
            ExprKind::Arrow { lhs, rhs, .. } => {
                self.infer(*lhs).product(&self.r.world, &self.infer(*rhs))
            }
            ExprKind::Compare { .. } => Type::formula(),
            ExprKind::IfThenElse {
                then_branch,
                else_branch,
                ..
            } => {
                let t = self.infer(*then_branch);
                let el = self.infer(*else_branch);
                if t.is_bool || el.is_bool {
                    Type::formula()
                } else {
                    t.union(&self.r.world, &el)
                }
            }
            ExprKind::Quant { quant, .. } => {
                if matches!(quant, Quant::Sum) {
                    Type::small_int(self.r.world.builtins.int)
                } else {
                    Type::formula()
                }
            }
            ExprKind::Comprehension { decls, .. } => self.infer_comprehension(decls),
            ExprKind::Let { body, .. } => self.infer(*body),
            ExprKind::Block(exprs) => {
                if let [only] = exprs.as_slice() {
                    self.infer(*only)
                } else {
                    Type::formula()
                }
            }
        }
    }

    fn infer_this(&self) -> Type {
        if let Some(t) = self.env_get("this") {
            return t;
        }
        self.rootsig.map_or_else(
            || Type::unary(self.r.world.builtins.univ),
            |s| self.r.world.sigs[s].ty.clone(),
        )
    }

    /// The bottom-up merge of a name's candidate types (no resolution). Mirrors
    /// [`Self::resolve_name`]'s candidate scope chain, returning the `ExprChoice`
    /// merge (or the leaf type for a single candidate).
    fn infer_name(&self, qn: &QualName, at_name: bool) -> Type {
        let segs = super::strip_this(qn.segments.iter().map(|s| s.text.clone()).collect());
        if !at_name && segs.len() == 1 {
            if let Some(t) = self.env_get(&segs[0]) {
                return t;
            }
        }
        if let Some(t) = self.builtin_value(&segs) {
            return t;
        }
        let cands = self.value_candidates(&segs, at_name);
        if cands.is_empty() {
            // A callable-by-name / macro / meta name: leniently `univ` (matches
            // `resolve_name`'s fallback, enough for sibling-arity slicing).
            return Type::unary(self.r.world.builtins.univ);
        }
        let mut merge = Type::empty();
        for c in &cands {
            merge = merge.merge(&self.r.world, &c.ty);
        }
        merge
    }

    fn infer_unary(&self, op: UnOp, e: ExprId) -> Type {
        let world = &self.r.world;
        match op {
            UnOp::Not
            | UnOp::No
            | UnOp::Some
            | UnOp::Lone
            | UnOp::One
            | UnOp::Always
            | UnOp::Eventually
            | UnOp::After
            | UnOp::Before
            | UnOp::Historically
            | UnOp::Once => Type::formula(),
            UnOp::SetOf | UnOp::ExactlyOf => self.infer(e).remove_bool_and_int(world.builtins.int),
            UnOp::SomeOf | UnOp::LoneOf | UnOp::OneOf => self.infer(e).extract(world, 1),
            UnOp::SeqOf => Type::unary(world.builtins.seq_int).product(world, &self.infer(e)),
            UnOp::Transpose => self.infer(e).transpose(world),
            UnOp::Closure => self.infer(e).closure(world),
            UnOp::ReflexiveClosure => {
                Type::product_of(vec![world.builtins.univ, world.builtins.univ])
                    .union(world, &self.infer(e).closure(world))
            }
            UnOp::Card | UnOp::IntOf | UnOp::SumOf => Type::small_int(world.builtins.int),
            UnOp::Prime => self.infer(e),
        }
    }

    fn infer_binary(&self, op: BinOp, lhs: ExprId, rhs: ExprId) -> Type {
        let world = &self.r.world;
        match op {
            BinOp::Or
            | BinOp::And
            | BinOp::Iff
            | BinOp::Implies
            | BinOp::Until
            | BinOp::Releases
            | BinOp::Since
            | BinOp::Triggered
            | BinOp::Seq => Type::formula(),
            BinOp::Join => unreachable!("join is inferred by infer_applicative"),
            BinOp::Union | BinOp::Override => self
                .infer(lhs)
                .union_with_common_arity(world, &self.infer(rhs)),
            BinOp::Intersect => self.infer(lhs).intersect(world, &self.infer(rhs)),
            BinOp::Diff => self.infer(lhs).pick_common_arity(world, &self.infer(rhs)),
            BinOp::DomRestrict => self.infer(rhs).domain_restrict(world, &self.infer(lhs)),
            BinOp::RanRestrict => self.infer(lhs).range_restrict(world, &self.infer(rhs)),
            BinOp::Shl
            | BinOp::Sha
            | BinOp::Shr
            | BinOp::IntAdd
            | BinOp::IntSub
            | BinOp::IntMul
            | BinOp::IntDiv
            | BinOp::IntRem => Type::small_int(world.builtins.int),
        }
    }

    fn infer_comprehension(&self, decls: &[DeclId]) -> Type {
        let mut ty: Option<Type> = None;
        for &d in decls {
            let decl = &self.ast().decls[d];
            let bt = self
                .infer(decl.bound)
                .remove_bool_and_int(self.r.world.builtins.int);
            for _ in &decl.names {
                ty = Some(match ty {
                    None => bt.clone(),
                    Some(prev) => prev.product(&self.r.world, &bt),
                });
            }
        }
        ty.unwrap_or_else(Type::empty)
    }

    /// Bottom-up type of a `.`-join / box-join / call spine (no resolution): the
    /// call's return type when a single applicable func/pred spine exists, else
    /// the relational join of the parts. An approximation sufficient for sibling
    /// slicing.
    fn infer_applicative(&self, e: ExprId) -> Type {
        // Builtin box targets.
        if let ExprKind::BoxJoin { target, args } = &self.expr(e).kind {
            if let ExprKind::Name(qn) = &self.expr(*target).kind {
                let joined = qn
                    .segments
                    .iter()
                    .map(|s| s.text.as_str())
                    .collect::<Vec<_>>()
                    .join("/");
                match joined.as_str() {
                    "pred/totalOrder" | "disj" => return Type::formula(),
                    "int" | "sum" => return Type::small_int(self.r.world.builtins.int),
                    "Int" => return Type::unary(self.r.world.builtins.int),
                    _ => {}
                }
            }
            let _ = args;
        }
        if let Some((mid, _)) = self.collect_macro_spine(e) {
            // Approximate a macro use by `univ` (its body type needs expansion).
            let _ = mid;
            return Type::unary(self.r.world.builtins.univ);
        }
        if let Some((cands, arg_exprs)) = self.collect_spine(e) {
            let n = arg_exprs.len();
            let rets: Vec<Type> = cands
                .iter()
                .filter(|c| c.params.len() == n)
                .map(|c| c.ret.clone())
                .collect();
            if !rets.is_empty() {
                let mut merge = Type::empty();
                for r in &rets {
                    merge = merge.merge(&self.r.world, r);
                }
                return merge;
            }
        }
        // Relational reading.
        match &self.expr(e).kind {
            ExprKind::Binary { lhs, rhs, .. } => {
                self.infer(*lhs).join(&self.r.world, &self.infer(*rhs))
            }
            ExprKind::BoxJoin { target, args } => {
                let mut acc = self.infer(*target);
                for &a in args {
                    acc = self.infer(a).join(&self.r.world, &acc);
                }
                acc
            }
            _ => Type::empty(),
        }
    }

    fn this_type(&mut self, span: Span) -> Type {
        if let Some(t) = self.env_get("this") {
            return t;
        }
        if let Some(s) = self.rootsig {
            return self.r.world.sigs[s].ty.clone();
        }
        // `this` outside any sig context: the reference rejects; lean to univ
        // rather than cascade (accept-lean, warnings secondary).
        let _ = span;
        Type::unary(self.r.world.builtins.univ)
    }

    // ---- names & candidates (§4.4) ----

    fn resolve_name(&mut self, qn: &QualName, want: &Want, at_name: bool) -> Type {
        let segs = super::strip_this(qn.segments.iter().map(|s| s.text.clone()).collect());

        // Local env (single-segment only) shadows everything (§4.4 step 2).
        // An `@name` reference never matches the lexical env: the reference does
        // `env.get(name)` with the `@` still attached, and env keys are bare, so
        // `@t` skips the quantifier/param var `t` and goes straight to the field
        // (resolution-doc §3.3 — `@` disables the implicit-`this` join *and* the
        // env shadow). Without this, `this.@t` inside `pred p[t: …]` wrongly
        // binds `@t` to the param `t`.
        if !at_name && segs.len() == 1 {
            if let Some(t) = self.env_get(&segs[0]) {
                self.used.insert(segs[0].clone());
                return t;
            }
        }

        // Builtin value names spelled with keywords / `fun/…` (§4.1/§4.5).
        if let Some(t) = self.builtin_value(&segs) {
            return t;
        }

        // A 0-param macro used as a value expands textually (§3.7).
        if let Some(mid) = self.lookup_macro(&segs) {
            if self.r.world.macros[mid].params.is_empty() {
                return self.expand_macro(mid, &[]);
            }
        }

        let cands = self.value_candidates(&segs, at_name);
        if cands.is_empty() {
            // A func/pred/macro name used as a bare value — e.g. a callable
            // passed as a macro argument (`interesting_not_axiom[Hb_p]`): treat
            // it leniently as `univ` so the textual substitution type-checks
            // (mettle binds macro params by type, not by expression).
            if !self.lookup_funcs(&segs).is_empty() || self.lookup_macro(&segs).is_some() {
                return Type::unary(self.r.world.builtins.univ);
            }
            // Meta names (`sig$`/`field$`, `X$.subfields`, …) are synthesized by
            // the meta phase, which mettle defers (resolution-doc §1 phase 8,
            // §9): in a `$`-bearing model, treat an otherwise-unknown name
            // leniently as `univ` rather than reject (the reference accepts;
            // LIMITATIONS).
            if segs.iter().any(|s| s.contains('$')) || self.r.graph.seen_dollar {
                return Type::unary(self.r.world.builtins.univ);
            }
            self.err(ResolveError::UnknownName {
                name: segs.join("/"),
                span: qn.span,
            });
            return Type::empty();
        }
        self.pick(&cands, want, &segs.join("/"), qn.span)
    }

    /// Looks up a macro by (possibly qualified) name across the reachable scope.
    fn lookup_macro(&self, raw: &[String]) -> Option<crate::world::MacroId> {
        let segs = super::strip_this(raw.to_vec());
        if segs.len() > 1 {
            let refs: Vec<&str> = segs.iter().map(String::as_str).collect();
            let (landing, consumed) = self.r.graph.walk_prefix(self.module, &refs, self.module);
            if consumed > 0 && consumed < segs.len() {
                let tail = &segs[consumed..];
                if tail.len() == 1 {
                    return self.r.mods[landing.index()].macros.get(&tail[0]).copied();
                }
            }
            return None;
        }
        for &rm in &self.r.reachable[self.module.index()] {
            if let Some(&id) = self.r.mods[rm.index()].macros.get(&segs[0]) {
                return Some(id);
            }
        }
        None
    }

    /// Expands a macro by textual substitution (resolution-doc §3.7): the
    /// argument types bind the macro's params, and the body is typed in the
    /// macro's defining module with the 20-unroll budget.
    fn expand_macro(&mut self, mid: crate::world::MacroId, arg_exprs: &[ExprId]) -> Type {
        if self.unroll == 0 {
            self.err(ResolveError::MacroTooDeep {
                span: self.r.world.macros[mid].span,
            });
            return Type::unary(self.r.world.builtins.univ);
        }
        // Argument types are evaluated in the caller's context.
        let arg_types: Vec<Type> = arg_exprs
            .iter()
            .map(|&a| self.check(a, &Want::Any))
            .collect();
        // A macro that receives a *callable passed by name* (a higher-order
        // macro: `interesting_not_axiom[some_pred]`) cannot be faithfully
        // type-checked by mettle's type-only param binding — the reference
        // substitutes the name textually so `param[args]` inside the body
        // becomes a real call, but mettle only has the param's (lenient `univ`)
        // type. Resolve such a body **accept-lean** (ADR-0009): mark it
        // ambiguous so the sort/arity rejects are suppressed and the
        // approximation never wrongly rejects a real model.
        let lean = arg_exprs.iter().any(|&a| self.arg_is_callable_by_name(a));
        let mac = self.r.world.macros[mid].clone();
        let mut sub = Cx::new(self.r, mac.module);
        sub.unroll = self.unroll - 1;
        sub.rootsig = self.rootsig;
        sub.ambig = lean;
        for (name, ty) in mac.params.iter().zip(&arg_types) {
            sub.env.push((name.clone(), ty.clone()));
        }
        let t = sub.check(mac.body, &Want::Any);
        self.errors.append(&mut sub.errors);
        self.warnings.append(&mut sub.warnings);
        t
    }

    /// Whether `e` is a bare name referring to a func/pred/macro that *takes
    /// arguments* — a callable passed by name, with no 0-ary value reading.
    /// Such an argument has no faithful value type in mettle's approximation
    /// (the reference substitutes it textually); a macro receiving one is
    /// resolved accept-lean (see [`Self::expand_macro`]).
    fn arg_is_callable_by_name(&self, e: ExprId) -> bool {
        let ExprKind::Name(qn) = &self.expr(e).kind else {
            return false;
        };
        let segs = super::strip_this(qn.segments.iter().map(|s| s.text.clone()).collect());
        // A local relation/param value is a value, not a global callable.
        if segs.len() == 1 && self.env_get(&segs[0]).is_some() {
            return false;
        }
        // A 0-ary value reading (sig, field, 0-ary fun) types fine as a value.
        if !self.value_candidates(&segs, false).is_empty() {
            return false;
        }
        let callable_func = self
            .lookup_funcs(&segs)
            .iter()
            .any(|&f| !self.r.world.funcs[f].params.is_empty());
        let callable_macro = self
            .lookup_macro(&segs)
            .is_some_and(|m| !self.r.world.macros[m].params.is_empty());
        callable_func || callable_macro
    }

    /// The reference's `ExprChoice.resolveHelper` (resolution-doc §4.4), now on
    /// **precise** types (mt-022): given the relevant type `t` derived from the
    /// position `want`, keep exact matches (`t.intersects(cand)` or both
    /// boolean), else legal matches (common arity), then the minimum-weight
    /// survivors; a single distinct type wins; several that all collapse to the
    /// same-arity empty set become `none`; otherwise it is a genuine ambiguity.
    ///
    /// At a **definite** position (a formula/int/set/`Of` slice) a residual
    /// ambiguity is the reference's "This name is ambiguous" reject. At a
    /// **lenient** position (`Any`, or a join slice mettle only approximates)
    /// mettle stays accept-lean — it picks the first min-weight candidate and
    /// flags `ambig` so downstream sort/arity checks are suppressed, since the
    /// reference's precise join/argument slice (which mettle does not compute
    /// there) might narrow to one.
    fn pick(&mut self, cands: &[Cand], want: &Want, name: &str, span: Span) -> Type {
        // A single candidate is not an `ExprChoice` at all (the reference's
        // `ExprChoice.make` shortcut): it resolves to itself, with no relevant-
        // type filter and no ambiguity — so a wrong relevant type here does not
        // suppress the parent's arity/sort check.
        if let [only] = cands {
            return only.ty.clone();
        }
        // A join position filters candidates by *joinability* with the sibling
        // (the reference's join slice), not by plain intersection — this is what
        // excludes a non-joinable implicit-`this` field (weight 0) in favour of
        // the cross-branch bare relation (weight 1) in `X.realm`. It is always a
        // lenient position (no ambiguity reject).
        if matches!(want, Want::JoinRhs(_) | Want::JoinLhs(_)) {
            let joinable: Vec<&Cand> = cands.iter().filter(|c| self.fits(&c.ty, want)).collect();
            // A join position that had **more than one** candidate is resolved
            // by mettle's *local* joinability filter, which can pick a reading
            // that is right for this join but wrong for an enclosing one (the
            // reference keeps every reading in an `ExprChoice` and resolves the
            // whole spine top-down — e.g. `s.grades.c` with a `Person`-owned and
            // a `Course`-owned `grades`). mettle cannot reconsider, so it flags
            // the surrounding join lenient, suppressing *only* the enclosing
            // illegal-join check (not the formula's sort/arity checks) that a
            // wrong local pick could spuriously trip.
            if cands.len() > 1 {
                self.join_lenient = true;
            }
            let pool: Vec<&Cand> = if joinable.is_empty() {
                cands.iter().collect()
            } else {
                joinable
            };
            let min_w = pool.iter().map(|c| c.weight).min().unwrap_or(0);
            let best: Vec<&Cand> = pool.into_iter().filter(|c| c.weight == min_w).collect();
            return best.first().map_or_else(Type::empty, |c| c.ty.clone());
        }

        let (relevant, lenient) = self.relevant_of(want, cands);
        // Exact matches, then (if none) legal (common-arity) matches.
        let exact: Vec<&Cand> = cands
            .iter()
            .filter(|c| self.choice_intersects(&c.ty, &relevant))
            .collect();
        let pool: Vec<&Cand> = if exact.is_empty() {
            cands
                .iter()
                .filter(|c| c.ty.has_common_arity(&relevant))
                .collect()
        } else {
            exact
        };
        // No candidate matches the relevant type at all. The reference errors
        // ("its relevant type does not intersect …"); mettle stays accept-lean
        // (this is a rare corner and risks false rejects), picking leniently.
        if pool.is_empty() {
            self.ambig = true;
            return cands.first().map_or_else(Type::empty, |c| c.ty.clone());
        }
        let min_w = pool.iter().map(|c| c.weight).min().unwrap_or(0);
        let best: Vec<&Cand> = pool.into_iter().filter(|c| c.weight == min_w).collect();

        let mut distinct: Vec<Type> = Vec::new();
        for c in &best {
            if !distinct.contains(&c.ty) {
                distinct.push(c.ty.clone());
            }
        }
        if distinct.len() == 1 {
            return distinct.into_iter().next().unwrap_or_else(Type::empty);
        }
        // All collapse to the same-arity empty set ⇒ `none` (§4.4 step 6).
        if distinct.iter().all(|t| t.is_error() || self.all_none(t)) {
            return Type::unary(self.r.world.builtins.none);
        }
        if lenient {
            self.ambig = true;
            return best.first().map_or_else(Type::empty, |c| c.ty.clone());
        }
        // A genuine ambiguity at a definite position (resolution-doc §4.4).
        self.err(ResolveError::AmbiguousName {
            name: name.to_owned(),
            span,
            candidates: Vec::new(),
        });
        best.first().map_or_else(Type::empty, |c| c.ty.clone())
    }

    /// Derives the relevant type `t` that `resolveHelper` filters against, from
    /// the position `want` and the candidate set, plus whether the position is
    /// **lenient** (mettle does not compute a precise-enough slice there, so it
    /// must not raise an ambiguity reject). `Set`/`Of` positions carry a precise
    /// relevant type; `Any` and the join-slice hints are lenient.
    fn relevant_of(&self, want: &Want, cands: &[Cand]) -> (Type, bool) {
        match want {
            Want::Formula => (Type::formula(), false),
            Want::Int => (Type::small_int(self.r.world.builtins.int), false),
            Want::Of(t) => (t.clone(), false),
            Want::OfLoose(t) => (t.clone(), true),
            Want::Set => {
                // `removesBoolAndInt` of the choice's own merged bounding type —
                // the set relevant type when no sibling narrows it further.
                let mut merge = Type::empty();
                for c in cands {
                    merge = merge.merge(&self.r.world, &c.ty);
                }
                (merge.remove_bool_and_int(self.r.world.builtins.int), false)
            }
            // A join-slice hint or an unconstrained position: keep every
            // candidate (its merge) but never raise ambiguity here.
            Want::Any | Want::SetLoose | Want::JoinRhs(_) | Want::JoinLhs(_) => {
                let mut merge = Type::empty();
                for c in cands {
                    merge = merge.merge(&self.r.world, &c.ty);
                }
                (merge, true)
            }
        }
    }

    /// The reference's `ExprChoice` exact-match test (`resolveHelper`): a
    /// candidate `cand` is an exact match for the relevant type `t` iff both are
    /// boolean, or their product types intersect (`Type.intersects`). The
    /// historical int↔Int coercion is dead (resolution-doc §4.5), so there is no
    /// int special case.
    fn choice_intersects(&self, cand: &Type, t: &Type) -> bool {
        (t.is_bool && cand.is_bool) || t.intersects(&self.r.world, cand)
    }

    /// Whether a value of type `ty` has the **sort** required at a `want`
    /// position (a formula where a formula is wanted, a relation where a set is
    /// wanted, an int where an int is wanted). Unlike [`Self::fits`], a set
    /// position rejects a boolean value — this is what keeps a bool pred-call
    /// (`util/integer` `pos`/`neg`/…) from being committed where the relational
    /// field-join reading is the one the reference's relevant type selects.
    fn sort_fits(&self, ty: &Type, want: &Want) -> bool {
        match want {
            Want::Any => true,
            Want::Formula => ty.is_bool,
            Want::Int => ty.is_small_int || ty.is_int(&self.r.world),
            Want::Set
            | Want::SetLoose
            | Want::Of(_)
            | Want::OfLoose(_)
            | Want::JoinRhs(_)
            | Want::JoinLhs(_) => !ty.is_bool && ty.has_entries(),
        }
    }

    fn fits(&self, ty: &Type, want: &Want) -> bool {
        match want {
            Want::Any | Want::Set | Want::SetLoose => true,
            Want::Formula => ty.is_bool,
            Want::Int => ty.is_small_int || ty.is_int(&self.r.world),
            // A candidate fits a join position only if the join yields a
            // *genuine* tuple (`has_tuple`) — a disjoint join now keeps a
            // `NONE`-headed product (mt-022), so `has_entries` would wrongly
            // admit a non-joinable candidate (`c.projects` picking `Person <:
            // projects` and collapsing to `none`).
            Want::JoinRhs(left) => {
                !ty.is_bool && left.join(&self.r.world, ty).has_tuple(&self.r.world)
            }
            Want::JoinLhs(right) => {
                !ty.is_bool && ty.join(&self.r.world, right).has_tuple(&self.r.world)
            }
            Want::Of(t) | Want::OfLoose(t) => {
                ty.intersects(&self.r.world, t)
                    || (ty.is_small_int && t.is_int(&self.r.world))
                    || (ty.is_int(&self.r.world) && t.is_small_int)
            }
        }
    }

    /// Builtin value names: `fun/max`, `fun/min`, `fun/next`, `fun/prev` (§4.5).
    /// These are synthesized by the parser as **single segments containing
    /// `/`**, so we match the joined form. `Int`/`String`/`seq/Int`/`univ`/
    /// `none` are handled as sigs by the builtin-sig lookup.
    fn builtin_value(&self, segs: &[String]) -> Option<Type> {
        let int = self.r.world.builtins.int;
        match segs.join("/").as_str() {
            "fun/max" | "fun/min" => Some(Type::unary(int)),
            "fun/next" | "fun/prev" => Some(Type::product_of(vec![int, int])),
            _ => None,
        }
    }

    /// Collects value candidates for a (possibly qualified) name: sigs/params,
    /// 0-ary funcs, and fields (with implicit-`this` inside a sig context).
    fn value_candidates(&self, segs: &[String], at_name: bool) -> Vec<Cand> {
        let mut out = Vec::new();

        // Sigs and module params (builtins folded in by lookup_sig_from).
        if let Some(sig) = self.r.lookup_sig_from(self.module, segs) {
            out.push(Cand {
                ty: self.r.world.sigs[sig].ty.clone(),
                weight: 0,
            });
        }

        // Zero-arg funcs/preds used as values: a 0-ary fun is its return value,
        // a 0-ary pred is a formula (`Geometry => …`). Weight 0 (`populate`
        // adds `ExprCall.make(f, null, penalty)` with penalty 0).
        for fid in self.lookup_funcs(segs) {
            let f = &self.r.world.funcs[fid];
            if f.params.is_empty() {
                out.push(Cand {
                    ty: if f.is_pred {
                        Type::formula()
                    } else {
                        f.return_ty.clone()
                    },
                    weight: 0,
                });
            }
        }

        // Fields by label (only the tail segment matters for bare labels).
        let label = &segs[segs.len() - 1];
        if segs.len() == 1 {
            self.collect_field_cands(label, at_name, &mut out);
        }
        out
    }

    /// Field candidates for a bare label (resolution-doc §3.3/§3.4, weights per
    /// `populate` resolution-mode 1):
    /// - `rootsig == None` (top level / pred body): the bare relation, weight 0.
    /// - inside a sig context whose `rootsig` is the same as or a descendant of
    ///   the field's owner: the implicit-`this` join (`this.f`), weight 0; or,
    ///   for `@f`, the bare relation, weight 0 (the `@` disables the join).
    /// - a cross-branch field (`rootsig` set but not descended from the owner):
    ///   the bare relation, weight **1** (the reference's "penalty of 1").
    fn collect_field_cands(&self, label: &str, at_name: bool, out: &mut Vec<Cand>) {
        for (fid, field) in self.r.world.fields.iter() {
            if field.name != *label {
                continue;
            }
            let owner_mod = self.r.world.sigs[field.owner].module;
            if !self.reachable_contains(owner_mod) {
                continue;
            }
            let _ = fid;
            match self.rootsig {
                None => out.push(Cand {
                    ty: field.ty.clone(),
                    weight: 0,
                }),
                Some(root) if self.r.world.sig_is_same_or_descendent(root, field.owner) => {
                    if at_name {
                        // `@f`: the bare relation, no implicit `this` join.
                        out.push(Cand {
                            ty: field.ty.clone(),
                            weight: 0,
                        });
                    } else {
                        let this_ty = self.r.world.sigs[root].ty.clone();
                        out.push(Cand {
                            ty: this_ty.join(&self.r.world, &field.ty),
                            weight: 0,
                        });
                    }
                }
                // Cross-branch: reachable via the bare relation, penalty 1.
                Some(_) => out.push(Cand {
                    ty: field.ty.clone(),
                    weight: 1,
                }),
            }
        }
    }

    fn reachable_contains(&self, m: ModuleId) -> bool {
        self.r.reachable[self.module.index()].contains(&m)
    }

    /// Looks up funcs/preds by (possibly qualified) name across the reachable
    /// scope chain (resolution-doc §4.4).
    fn lookup_funcs(&self, raw: &[String]) -> Vec<FuncId> {
        let segs = super::strip_this(raw.to_vec());
        let segs = &segs[..];
        let mut out = Vec::new();
        if segs.len() > 1 {
            let refs: Vec<&str> = segs.iter().map(String::as_str).collect();
            let (landing, consumed) = self.r.graph.walk_prefix(self.module, &refs, self.module);
            // A qualified prefix that matched no alias (`consumed == 0`) is a
            // genuine qualified-lookup failure — no unqualified fallback (else
            // `Color/first` would wrongly find a bare `first`, probe 09).
            if consumed == 0 {
                return out;
            }
            if consumed < segs.len() {
                let tail = &segs[consumed..];
                if tail.len() == 1 {
                    if let Some(v) = self.r.mods[landing.index()].funcs.get(&tail[0]) {
                        out.extend_from_slice(v);
                    }
                }
            }
            return out;
        }
        let bare = &segs[segs.len() - 1];
        for &rm in &self.r.reachable[self.module.index()] {
            if let Some(v) = self.r.mods[rm.index()].funcs.get(bare) {
                for &fid in v {
                    if !out.contains(&fid) {
                        out.push(fid);
                    }
                }
            }
        }
        out
    }

    // ---- operators ----

    fn unary(&mut self, op: UnOp, e: ExprId, span: Span, want: &Want) -> Type {
        match op {
            // Formula prefixes.
            UnOp::Not => {
                self.check(e, &Want::Formula);
                Type::formula()
            }
            UnOp::No | UnOp::Some | UnOp::Lone | UnOp::One => {
                self.check(e, &Want::Set);
                Type::formula()
            }
            // Multiplicity bound markers: the operand's set type unchanged.
            UnOp::SetOf | UnOp::SomeOf | UnOp::LoneOf | UnOp::OneOf | UnOp::ExactlyOf => {
                self.check(e, &Want::Set)
            }
            // `seq A` bound: prepend the seq-index column (§4.5).
            UnOp::SeqOf => {
                let t = self.check(e, &Want::SetLoose);
                Type::unary(self.r.world.builtins.seq_int).product(&self.r.world, &t)
            }
            // Relational unary: `~`/`^`/`*` require a binary operand
            // (resolution-doc §4.2). The reference computes the arity error
            // bottom-up regardless of the top-down type.
            UnOp::Transpose => {
                let t = self.check(e, &Want::SetLoose);
                self.require_binary(&t, "~", span);
                t.transpose(&self.r.world)
            }
            UnOp::Closure | UnOp::ReflexiveClosure => {
                // A closure preserves the operand's binary shape, so a relevant
                // type from the parent (e.g. `i.*next`'s `JoinRhs`) flows
                // straight to the operand to disambiguate it.
                let operand_want = match want {
                    Want::JoinRhs(_) => want,
                    _ => &Want::SetLoose,
                };
                let t = self.check(e, operand_want);
                self.require_binary(
                    &t,
                    if matches!(op, UnOp::Closure) {
                        "^"
                    } else {
                        "*"
                    },
                    span,
                );
                // `*` includes `univ->univ`.
                if matches!(op, UnOp::ReflexiveClosure) {
                    Type::product_of(vec![self.r.world.builtins.univ, self.r.world.builtins.univ])
                        .union(&self.r.world, &t)
                } else {
                    t
                }
            }
            // Integer casts.
            UnOp::Card | UnOp::IntOf | UnOp::SumOf => {
                self.check(e, &Want::Set);
                Type::small_int(self.r.world.builtins.int)
            }
            // Temporal unary: type like the operand (formula/relation preserved).
            UnOp::Always
            | UnOp::Eventually
            | UnOp::After
            | UnOp::Before
            | UnOp::Historically
            | UnOp::Once => {
                let _ = want;
                self.check(e, &Want::Formula);
                Type::formula()
            }
            UnOp::Prime => self.check(e, &Want::SetLoose),
        }
    }

    fn binary(&mut self, op: BinOp, lhs: ExprId, rhs: ExprId, span: Span) -> Type {
        match op {
            // Logical / temporal binaries → FORMULA.
            BinOp::Or
            | BinOp::And
            | BinOp::Iff
            | BinOp::Implies
            | BinOp::Until
            | BinOp::Releases
            | BinOp::Since
            | BinOp::Triggered
            | BinOp::Seq => {
                self.check(lhs, &Want::Formula);
                self.check(rhs, &Want::Formula);
                Type::formula()
            }
            // Join is routed through `applicative` before reaching `binary`.
            BinOp::Join => unreachable!("join is handled by applicative"),
            // Set ops needing common arity. The right operand is resolved with
            // the left type as a relevant hint (`Of`), which disambiguates
            // overloaded names like `Time - first` (§4.3). `Of` only filters —
            // `pick` falls back to the full candidate pool if it empties — so a
            // legitimately different-typed operand (`Man + Woman`) is unharmed.
            BinOp::Union | BinOp::Intersect | BinOp::Diff | BinOp::Override => {
                // `+`/`&`/`-`/`++` slice each operand by `intersect(p)` in the
                // reference, so both are lenient set positions (an overloaded
                // operand like `prev + next` is narrowed by the parent relevant
                // type, which mettle approximates).
                let l = self.check(lhs, &Want::SetLoose);
                let r = if l.is_error() {
                    self.check(rhs, &Want::SetLoose)
                } else {
                    self.check(rhs, &Want::OfLoose(l.clone()))
                };
                if !l.is_error() && !r.is_error() && !l.has_common_arity(&r) && !self.ambig {
                    self.err(ResolveError::ArityMismatch {
                        op: bin_sym(op),
                        span,
                    });
                    return Type::empty();
                }
                match op {
                    BinOp::Intersect => l.intersect(&self.r.world, &r),
                    BinOp::Diff => l,
                    _ => l.union(&self.r.world, &r),
                }
            }
            // Domain restriction `A <: r`: the domain `A` must be a **unary**
            // set (`ExprBinary.make` DOMAIN → `r.domainRestrict(A)`, EMPTY ⇒
            // "This must be a unary set" at `A`). Its first column also
            // disambiguates `r`'s fields the same way a join does.
            BinOp::DomRestrict => {
                let l = self.check(lhs, &Want::SetLoose);
                let r = self.check(rhs, &Want::JoinRhs(l.clone()));
                let ty = r.domain_restrict(&self.r.world, &l);
                self.check_restrict_unary(&l, &r, &ty, self.expr(lhs).span);
                ty
            }
            // Range restriction `r :> A`: the range `A` (rhs) must be unary.
            BinOp::RanRestrict => {
                let l = self.check(lhs, &Want::SetLoose);
                let r = self.check(rhs, &Want::SetLoose);
                let ty = l.range_restrict(&self.r.world, &r);
                self.check_restrict_unary(&l, &r, &ty, self.expr(rhs).span);
                ty
            }
            // Integer binops (`fun/add` …, shifts): both int → small int.
            BinOp::Shl
            | BinOp::Sha
            | BinOp::Shr
            | BinOp::IntAdd
            | BinOp::IntSub
            | BinOp::IntMul
            | BinOp::IntDiv
            | BinOp::IntRem => {
                self.check(lhs, &Want::Int);
                self.check(rhs, &Want::Int);
                Type::small_int(self.r.world.builtins.int)
            }
        }
    }

    fn arrow(&mut self, lhs: ExprId, rhs: ExprId) -> Type {
        // Arrow operands are lenient set positions: the reference slices each by
        // `p.intersect(product)`, which mettle approximates.
        let l = self.check(lhs, &Want::SetLoose);
        let r = self.check(rhs, &Want::SetLoose);
        l.product(&self.r.world, &r)
    }

    fn compare(&mut self, op: CmpOp, lhs: ExprId, rhs: ExprId, span: Span) -> Type {
        match op {
            CmpOp::Lt | CmpOp::Gt | CmpOp::Le | CmpOp::Ge => {
                // Arithmetic comparisons: both sides typechecked as int.
                self.check(lhs, &Want::Int);
                self.check(rhs, &Want::Int);
                Type::formula()
            }
            CmpOp::Eq | CmpOp::In => {
                // The reference's relevant slices for `=`/`in` (ExprBinary.resolve):
                // the left is sliced to the arities it shares with the right
                // (`pickCommonArity`), the right to its intersection with that
                // left slice. These require both bottom-up types, computed via
                // `infer` (a pure sibling-type peek). This precision is what
                // distinguishes a real ambiguity (`projects in Course->Project`:
                // both same-arity fields survive) from an arity-narrowed unique
                // pick (`keys in Room lone->Key`: only the arity-2 field).
                let lt = self.infer(lhs);
                let rt = self.infer(rhs);
                let a = lt.pick_common_arity(&self.r.world, &rt);
                let b = rt.intersect(&self.r.world, &a);
                let l = self.check(lhs, &Want::Of(a));
                let r = self.check(rhs, &Want::Of(b));
                let both_int = l.is_int(&self.r.world) && r.is_int(&self.r.world);
                let ok = l.is_error() || r.is_error() || l.has_common_arity(&r) || both_int;
                if !ok && !self.ambig {
                    self.err(ResolveError::ArityMismatch {
                        op: if matches!(op, CmpOp::Eq) { "=" } else { "in" },
                        span,
                    });
                }
                Type::formula()
            }
        }
    }

    fn if_then_else(&mut self, cond: ExprId, then_e: ExprId, else_e: ExprId, want: &Want) -> Type {
        self.check(cond, &Want::Formula);
        let t = self.check(then_e, want);
        let e = self.check(else_e, want);
        if t.is_bool || e.is_bool {
            Type::formula()
        } else {
            t.union(&self.r.world, &e)
        }
    }

    // ---- application vs relational join (§4.4) ----

    /// Resolves a `.`-join or box-join node. First tries the **applicative**
    /// reading — a func/pred spine gathering args from leading `.`-joins and
    /// trailing `[…]` (so `x.f`, `f[x]`, and `x.f[y]` all become `f[x(,y)]`,
    /// resolution-doc §4.4 box-join completion). Falls back to a relational
    /// join / box join when no candidate applies.
    #[allow(clippy::too_many_lines)] // one cohesive dispatch: builtins, macros, calls, relational
    fn applicative(&mut self, e: ExprId, span: Span, want: &Want) -> Type {
        // Set when a func/pred spine was collected but no call applied — the
        // relational reading is then a *failed call*, whose reject is `BadCall`,
        // not `IllegalJoin` (resolution-doc §4.4).
        let mut from_call_spine = false;
        // Builtin box-join targets: list preds and the `int`/`Int` casts.
        if let ExprKind::BoxJoin { target, args } = &self.expr(e).kind {
            if let ExprKind::Name(qn) = &self.expr(*target).kind {
                // Synthesized builtin names are single `/`-joined segments.
                let joined = qn
                    .segments
                    .iter()
                    .map(|s| s.text.as_str())
                    .collect::<Vec<_>>()
                    .join("/");
                let args = args.clone();
                match joined.as_str() {
                    "pred/totalOrder" | "disj" => {
                        // The reference gives each arg a precise unary relevant
                        // type (`args[0].pickUnary()`, `t.product(t)`); mettle
                        // approximates with a lenient set position.
                        for a in args {
                            self.check(a, &Want::SetLoose);
                        }
                        return Type::formula();
                    }
                    // `int[e]`/`sum[e]`: cast a set of `Int` atoms to a
                    // primitive int (the bracketed spelling of `int e`/`sum e`).
                    "int" | "sum" => {
                        for a in args {
                            self.check(a, &Want::SetLoose);
                        }
                        return Type::small_int(self.r.world.builtins.int);
                    }
                    // `Int[e]`: cast a primitive int to the `Int` sig atom.
                    "Int" => {
                        for a in args {
                            self.check(a, &Want::Any);
                        }
                        return Type::unary(self.r.world.builtins.int);
                    }
                    _ => {}
                }
            }
        }

        // A parameterized macro applied via box join or `.`-spine expands
        // textually (§3.7): `m[a]`, `x.m[a]` (= `m[x,a]`), and `x.m`.
        if let Some((mid, arg_exprs)) = self.collect_macro_spine(e) {
            return self.expand_macro(mid, &arg_exprs);
        }

        if let Some((cands, arg_exprs)) = self.collect_spine(e) {
            // Type args with the parameter types when the arity uniquely picks a
            // candidate (disambiguates overloaded args like `init[first]`).
            let arity_cands: Vec<&CallCand> = cands
                .iter()
                .filter(|c| c.params.len() == arg_exprs.len())
                .collect();
            let arg_types: Vec<Type> = if arity_cands.len() == 1 {
                let params = arity_cands[0].params.clone();
                arg_exprs
                    .iter()
                    .zip(&params)
                    .map(|(&a, p)| self.check(a, &Want::OfLoose(p.clone())))
                    .collect()
            } else {
                arg_exprs
                    .iter()
                    .map(|&a| self.check(a, &Want::Any))
                    .collect()
            };
            // `applicable` (resolution-doc §4.4): a candidate whose arity
            // matches and whose every argument is *applicable* to its parameter
            // — common arity, and (only when **both** arg and param are
            // non-empty) intersecting. An empty (`{none}`) argument is always
            // applicable, exactly as the reference (`Context.applicable`): this
            // is why `max[(c.grades).Student]` resolves as a call even when the
            // receiver is statically empty.
            let matches: Vec<&CallCand> = cands
                .iter()
                .filter(|c| c.params.len() == arg_exprs.len() && self.args_apply(c, &arg_types))
                .collect();
            let chosen: Option<&CallCand> = match matches.len() {
                0 => None, // no applicable call → try the relational reading
                1 => {
                    // A single applicable call. The reference keeps *both* the
                    // call reading and the relational/field-join reading in an
                    // `ExprChoice` and picks by the relevant type. mettle commits
                    // to the call when it genuinely applies (a non-empty argument
                    // truly intersects the parameter) or when its return fits the
                    // relevant type; otherwise — a call that applies only because
                    // an argument is empty (`{none}`), whose return does not fit —
                    // it falls through to the relational reading. This is what
                    // stops `t.pos` (field `pos` vs auto-opened `util/integer`
                    // `pred pos`, empty receiver) from committing to the bool
                    // pred where a set is wanted.
                    let c = matches[0];
                    if self.sort_fits(&c.ret, want) || self.args_apply_strict(c, &arg_types) {
                        Some(c)
                    } else {
                        None
                    }
                }
                _ => {
                    // Several applicable candidates: the reference's `ExprChoice`
                    // narrows by the **relevant type** pushed from the parent
                    // (min-weight → resolve-and-retry). mettle keeps only those
                    // whose return fits the relevant type; if that leaves exactly
                    // one it wins, else the "This name is ambiguous" reject
                    // (probe 15). When the arguments only match *vacuously*
                    // (every candidate applies because an argument is empty),
                    // resolve accept-lean rather than risk a false reject.
                    let by_want: Vec<&CallCand> = matches
                        .iter()
                        .copied()
                        .filter(|c| self.fits(&c.ret, want))
                        .collect();
                    if by_want.len() == 1 {
                        Some(by_want[0])
                    } else {
                        let any_strict = matches
                            .iter()
                            .any(|c| self.args_apply_strict(c, &arg_types));
                        let pool = if by_want.is_empty() {
                            &matches
                        } else {
                            &by_want
                        };
                        if any_strict {
                            self.err(ResolveError::AmbiguousName {
                                name: cands[0].reason.clone(),
                                span,
                                candidates: pool.iter().map(|c| c.reason.clone()).collect(),
                            });
                        } else {
                            self.ambig = true;
                        }
                        Some(pool[0])
                    }
                }
            };
            if let Some(c) = chosen {
                if self.no_calls {
                    self.err(ResolveError::FieldBoundHasCall {
                        name: self.field_name.clone(),
                        span,
                    });
                }
                return c.ret.clone();
            }
            // No applicable call: fall through to the relational reading, but
            // remember a call spine existed so its failure is a `BadCall`, never
            // an `IllegalJoin` (resolution-doc §4.4 `process`).
            from_call_spine = true;
        }

        // Relational reading.
        match &self.expr(e).kind {
            ExprKind::Binary { lhs, rhs, .. } => {
                let (lhs, rhs) = (*lhs, *rhs);
                // Track whether *this* join's operands involved a multi-candidate
                // joinability pick (a possibly-wrong local commitment), so the
                // enclosing illegal-join check can be suppressed without touching
                // the formula-wide `ambig`.
                let saved_jl = self.join_lenient;
                self.join_lenient = false;
                // Both operands of a relational join are lenient set positions:
                // mettle only approximates the reference's precise per-column
                // join slice (which also depends on the *parent* relevant type,
                // not threaded here), so an overloaded operand must never raise
                // an ambiguity reject — the reference narrows `first.next` /
                // `prev.t"` and even field overloads (`key`/`name`) by that
                // parent type, which mettle lacks. Left-of-join ambiguities the
                // jar still rejects (`projects.p`) stay a documented
                // over-acceptance (the single-pass limitation).
                let l = self.check(lhs, &Want::SetLoose);
                let r = self.check(rhs, &Want::JoinRhs(l.clone()));
                let joined = l.join(&self.r.world, &r);
                // Join-retry (§4.4): if the left was an overloaded bare name that
                // resolved to the wrong candidate (empty join), re-resolve it
                // with the right operand as a `JoinLhs` hint.
                let joined =
                    if joined.has_entries() || !matches!(self.expr(lhs).kind, ExprKind::Name(_)) {
                        joined
                    } else {
                        let r2 = self.check(rhs, &Want::Set);
                        let l2 = self.check(lhs, &Want::JoinLhs(r2.clone()));
                        l2.join(&self.r.world, &r2)
                    };
                let operands_lenient = self.join_lenient;
                if !from_call_spine && !operands_lenient {
                    self.check_illegal_join(&l, &r, &joined, span);
                }
                // Propagate leniency to any enclosing join.
                self.join_lenient = saved_jl || operands_lenient;
                joined
            }
            ExprKind::BoxJoin { target, args } => {
                // `m[a,b] = b.(a.m)`: the first arg joins the target, so it is a
                // relevant hint that disambiguates an overloaded target name
                // (`next[first]` = `first.next`).
                let (target, args) = (*target, args.clone());
                let arg_types: Vec<Type> =
                    args.iter().map(|&a| self.check(a, &Want::Any)).collect();
                let target_want = arg_types
                    .first()
                    .map_or(Want::Set, |t| Want::JoinRhs(t.clone()));
                let mut acc = self.check(target, &target_want);
                for at in &arg_types {
                    // A box-join's desugaring to joins is *not* a source of the
                    // `ExprBadJoin` reject: a failed `m[a,b]` is a `BadCall`, not
                    // an illegal join (resolution-doc §4.4 `process`). Only the
                    // genuine binary `.`-join arm below fires `IllegalJoin`.
                    acc = at.join(&self.r.world, &acc);
                }
                acc
            }
            _ => Type::empty(),
        }
    }

    /// Collects the func/pred spine of an application: the candidate funcs plus
    /// the argument expressions in order (leading `.`-join args first, then
    /// box-join args). `None` when `e` has no func head (a pure relation).
    fn collect_spine(&self, e: ExprId) -> Option<(Vec<CallCand>, Vec<ExprId>)> {
        match &self.expr(e).kind {
            ExprKind::Name(qn) => {
                let segs: Vec<String> = qn.segments.iter().map(|s| s.text.clone()).collect();
                let cands = self.call_candidates_for(&segs);
                if cands.is_empty() {
                    None
                } else {
                    Some((cands, Vec::new()))
                }
            }
            ExprKind::BoxJoin { target, args } => {
                let (cands, mut pre) = self.collect_spine(*target)?;
                pre.extend_from_slice(args);
                Some((cands, pre))
            }
            ExprKind::Binary {
                op: BinOp::Join,
                lhs,
                rhs,
            } => {
                // `x.f` applies f to x when f is a func/pred name.
                let segs: Vec<String> = match &self.expr(*rhs).kind {
                    ExprKind::Name(qn) => qn.segments.iter().map(|s| s.text.clone()).collect(),
                    _ => return None,
                };
                let cands = self.call_candidates_for(&segs);
                if cands.is_empty() {
                    None
                } else {
                    Some((cands, vec![*lhs]))
                }
            }
            _ => None,
        }
    }

    /// Collects a macro-application spine (§3.7): the macro plus its argument
    /// expressions gathered from a leading `.`-join and trailing box args, so
    /// `m[a]`, `x.m[a]`, and `x.m` all expand. `None` when the head is not a
    /// (parameterized) macro. A 0-param macro used bare is handled in
    /// `resolve_name`, so only param-macros or applied macros reach here.
    fn collect_macro_spine(&self, e: ExprId) -> Option<(crate::world::MacroId, Vec<ExprId>)> {
        match &self.expr(e).kind {
            ExprKind::Name(qn) => {
                let segs: Vec<String> = qn.segments.iter().map(|s| s.text.clone()).collect();
                let mid = self.lookup_macro(&segs)?;
                if self.r.world.macros[mid].params.is_empty() {
                    None
                } else {
                    Some((mid, Vec::new()))
                }
            }
            ExprKind::BoxJoin { target, args } => {
                let (mid, mut pre) = self.collect_macro_spine(*target)?;
                pre.extend_from_slice(args);
                Some((mid, pre))
            }
            ExprKind::Binary {
                op: BinOp::Join,
                lhs,
                rhs,
            } => {
                let segs: Vec<String> = match &self.expr(*rhs).kind {
                    ExprKind::Name(qn) => qn.segments.iter().map(|s| s.text.clone()).collect(),
                    _ => return None,
                };
                let mid = self.lookup_macro(&segs)?;
                Some((mid, vec![*lhs]))
            }
            _ => None,
        }
    }

    /// Call candidates (funcs/preds) for a name, unless a local env var shadows
    /// it (then it is a value/relation, not a call target).
    fn call_candidates_for(&self, segs: &[String]) -> Vec<CallCand> {
        if segs.len() == 1 && self.env_get(&segs[0]).is_some() {
            return Vec::new();
        }
        let mut out = Vec::new();
        for fid in self.lookup_funcs(segs) {
            let f = &self.r.world.funcs[fid];
            out.push(CallCand {
                ret: f.return_ty.clone(),
                params: f.params.iter().map(|p| p.ty.clone()).collect(),
                reason: format!("{} {}", if f.is_pred { "pred" } else { "fun" }, f.name),
            });
        }
        out
    }

    /// Whether every argument type intersects its parameter type (arity + type
    /// applicability, resolution-doc §4.4).
    fn args_apply(&self, c: &CallCand, arg_types: &[Type]) -> bool {
        let w = &self.r.world;
        c.params.iter().zip(arg_types).all(|(p, a)| {
            if a.is_error() || p.is_error() {
                return true; // an error-typed arg/param can't decide applicability
            }
            if !a.has_common_arity(p) {
                return false;
            }
            // Only a *non-empty* arg against a *non-empty* param can fail to
            // apply (an empty `{none}` operand is vacuously applicable).
            !(a.has_tuple(w) && p.has_tuple(w) && !a.intersects(w, p))
        })
    }

    /// Whether every argument *genuinely* (non-vacuously) intersects its
    /// parameter — used only to tell a real overload ambiguity (probe 15) from
    /// one manufactured by an empty/under-typed argument (the ambiguity branch
    /// of [`Self::applicative`]).
    fn args_apply_strict(&self, c: &CallCand, arg_types: &[Type]) -> bool {
        let w = &self.r.world;
        c.params
            .iter()
            .zip(arg_types)
            .all(|(p, a)| a.has_tuple(w) && p.has_tuple(w) && a.intersects(w, p))
    }

    // ---- binders ----

    fn quant(&mut self, quant: Quant, decls: &[DeclId], body: ExprId, span: Span) -> Type {
        let pushed = self.bind_decls(decls);
        if matches!(quant, Quant::Sum) {
            self.check(body, &Want::Int);
        } else {
            self.check(body, &Want::Formula);
        }
        self.pop_and_warn_unused(decls, pushed);
        let _ = span;
        if matches!(quant, Quant::Sum) {
            Type::small_int(self.r.world.builtins.int)
        } else {
            Type::formula()
        }
    }

    fn comprehension(&mut self, decls: &[DeclId], body: ExprId) -> Type {
        let pushed = self.bind_decls(decls);
        self.check(body, &Want::Formula);
        // Comprehension type = product of the decl bound types, in order.
        let mut ty: Option<Type> = None;
        for &d in decls {
            let decl = &self.ast().decls[d];
            let bt = self.decl_bound_type(decl);
            for _ in &decl.names {
                ty = Some(match ty {
                    None => bt.clone(),
                    Some(prev) => prev.product(&self.r.world, &bt),
                });
            }
        }
        self.pop_and_warn_unused(decls, pushed);
        ty.unwrap_or_else(Type::empty)
    }

    fn let_expr(&mut self, bindings: &[LetBinding], body: ExprId, want: &Want) -> Type {
        let mut pushed = 0;
        for b in bindings {
            let t = self.check(b.value, &Want::Any);
            self.env.push((b.name.text.clone(), t));
            pushed += 1;
        }
        let out = self.check(body, want);
        for _ in 0..pushed {
            self.env.pop();
        }
        out
    }

    /// Binds a decl list into the env, returning how many env frames to pop.
    fn bind_decls(&mut self, decls: &[DeclId]) -> usize {
        let mut pushed = 0;
        for &d in decls {
            let decl = self.ast().decls[d].clone();
            let bt = self.decl_bound_type(&decl);
            for name in &decl.names {
                self.env.push((name.text.clone(), bt.clone()));
                pushed += 1;
            }
        }
        pushed
    }

    /// The (element) type each variable of a decl ranges over.
    fn decl_bound_type(&mut self, decl: &Decl) -> Type {
        let t = self.check(decl.bound, &Want::Set);
        t.as_set(self.r.world.builtins.int)
    }

    fn pop_and_warn_unused(&mut self, decls: &[DeclId], pushed: usize) {
        // Collect names before popping (best-effort unused-binder warning).
        let mut names: Vec<(String, Span)> = Vec::new();
        for &d in decls {
            let decl = &self.ast().decls[d];
            for n in &decl.names {
                names.push((n.text.clone(), n.span));
            }
        }
        for _ in 0..pushed {
            self.env.pop();
        }
        for (name, span) in names {
            if !self.used.contains(&name) {
                self.warnings
                    .push(ResolveWarning::UnusedVariable { name, span });
            }
        }
    }

    // ---- helpers ----

    /// Rejects `~`/`^`/`*` on a non-binary operand (resolution-doc §4.2). A
    /// binary type has entries, all of arity 2. Suppressed on error/ambiguous
    /// operands (accept-lean, ADR-0009) — a wrong arity there may be an artifact
    /// of an arbitrary overload pick, not a genuine mismatch.
    fn require_binary(&mut self, t: &Type, op: &'static str, span: Span) {
        if self.ambig || t.is_error() {
            return;
        }
        if !(t.has_entries() && t.entries.iter().all(|p| p.arity() == 2)) {
            self.err(ResolveError::UnaryNotBinary { op, span });
        }
    }

    /// Fires `IllegalJoin` (`ExprBadJoin`, resolution-doc §4.2/§4.4) when a
    /// relational join's type is the true `EMPTY` sentinel — which, with the
    /// faithful [`Type::join`] (mt-022), happens iff **both** operands are
    /// entirely unary (every arity-0 join is dropped, leaving no product).
    /// A disjoint *multi-hop* join instead yields a `NONE`-headed product of the
    /// correct arity (`has_entries` true) — a legal but statically-empty join —
    /// so this never fires there. Guarded by the accept-lean bias
    /// (`self.ambig` / error-typed operands) so an artifact of an arbitrary
    /// overload pick is never rejected.
    fn check_illegal_join(&mut self, l: &Type, r: &Type, joined: &Type, span: Span) {
        if self.ambig || self.r.graph.seen_dollar || l.is_bool || r.is_bool {
            return;
        }
        // A lenient `univ` placeholder (an unknown/meta/callable-by-name that
        // mettle resolves to `univ` rather than reject) must never trigger the
        // reject — those are exactly the leaves the reference resolves precisely
        // and mettle approximates. Real illegal joins (`Teacher.Person`) join
        // two concrete unary sigs, never `univ`.
        if l.has_entries()
            && r.has_entries()
            && joined.is_error()
            && !self.contains_univ(l)
            && !self.contains_univ(r)
        {
            self.err(ResolveError::IllegalJoin { span });
        }
    }

    /// Fires `NotUnarySet` when a domain/range restriction (`<:` / `:>`)
    /// produced the `EMPTY` sentinel because its restricting operand is not a
    /// unary set (`ExprBinary.make` DOMAIN/RANGE, resolution-doc §4.2). Guarded
    /// by the accept-lean bias (`ambig`/`join_lenient`, error/bool operands).
    fn check_restrict_unary(&mut self, l: &Type, r: &Type, ty: &Type, span: Span) {
        if self.ambig || self.join_lenient || l.is_bool || r.is_bool {
            return;
        }
        if !l.is_error() && !r.is_error() && ty.is_error() {
            self.err(ResolveError::NotUnarySet { span });
        }
    }

    /// Whether any product column of `t` is `univ` — a signal of a lenient
    /// placeholder (or the genuine top sig), excluded from `IllegalJoin`.
    fn contains_univ(&self, t: &Type) -> bool {
        let univ = self.r.world.builtins.univ;
        t.entries.iter().any(|p| p.0.contains(&univ))
    }

    fn env_get(&self, name: &str) -> Option<Type> {
        self.env
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, t)| t.clone())
    }

    /// Whether every column of every product is `none` (an all-empty bound).
    fn all_none(&self, t: &Type) -> bool {
        t.has_entries()
            && t.entries
                .iter()
                .all(|p| p.0.iter().all(|&s| s == self.r.world.builtins.none))
    }
}

/// The display symbol of a binary operator for arity-mismatch messages.
fn bin_sym(op: BinOp) -> &'static str {
    match op {
        BinOp::Union => "+",
        BinOp::Intersect => "&",
        BinOp::Diff => "-",
        BinOp::Override => "++",
        _ => "<op>",
    }
}
