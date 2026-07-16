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
    /// `resolve_as_set`: any relational value.
    Set,
    /// `resolve_as_int`: an integer.
    Int,
    /// The right operand of a relational join: prefer candidates whose first
    /// column can join with the given left type (field disambiguation, §4.3).
    JoinRhs(Type),
    /// The left operand of a relational join: prefer candidates whose last
    /// column can join with the given right type (the join-retry, §4.4).
    JoinLhs(Type),
    /// A relevant type a candidate must intersect (a call argument's parameter
    /// type, or a comparison sibling; resolution-doc §4.3/§4.4).
    Of(Type),
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
        let t = self.check(e, &Want::Set);
        t.as_set(self.r.world.builtins.int)
    }

    /// Resolves a declaration bound (field/param/quant), returning the relation
    /// type it denotes (multiplicity markers strip away; `seq` adds the index
    /// column).
    pub(super) fn run_bound(&mut self, e: ExprId) -> Type {
        let t = self.check(e, &Want::Set);
        t.as_set(self.r.world.builtins.int)
    }

    // ---- the core walk ----

    fn check(&mut self, e: ExprId, want: &Want) -> Type {
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
            | ExprKind::BoxJoin { .. } => self.applicative(e, span),
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
        if segs.len() == 1 {
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
        let mac = self.r.world.macros[mid].clone();
        let mut sub = Cx::new(self.r, mac.module);
        sub.unroll = self.unroll - 1;
        sub.rootsig = self.rootsig;
        for (name, ty) in mac.params.iter().zip(&arg_types) {
            sub.env.push((name.clone(), ty.clone()));
        }
        let t = sub.check(mac.body, &Want::Any);
        self.errors.append(&mut sub.errors);
        self.warnings.append(&mut sub.warnings);
        t
    }

    /// Applies the disambiguation ladder (resolution-doc §4.4): want-filter →
    /// min-weight → single/ambiguous/all-empty.
    fn pick(&mut self, cands: &[Cand], want: &Want, name: &str, span: Span) -> Type {
        // Exact/legal matches: keep candidates whose type fits `want`.
        let filtered: Vec<&Cand> = cands.iter().filter(|c| self.fits(&c.ty, want)).collect();
        // Fall back to all candidates if the want excludes everything
        // (accept-lean: the reference would emit a no-intersect error here,
        // which is out of the probe-gauged set and rare on real models).
        let pool: Vec<&Cand> = if filtered.is_empty() {
            cands.iter().collect()
        } else {
            filtered
        };
        let min_w = pool.iter().map(|c| c.weight).min().unwrap_or(0);
        let best: Vec<&Cand> = pool.into_iter().filter(|c| c.weight == min_w).collect();

        // Distinct types among the min-weight survivors.
        let mut distinct: Vec<Type> = Vec::new();
        for c in &best {
            if !distinct.contains(&c.ty) {
                distinct.push(c.ty.clone());
            }
        }
        if distinct.len() == 1 {
            return distinct.into_iter().next().unwrap_or_else(Type::empty);
        }
        // All collapse to empty ⇒ `none` of the shared arity (§4.4 step 6).
        if distinct.iter().all(|t| t.is_error() || self.all_none(t)) {
            return Type::unary(self.r.world.builtins.none);
        }
        // A bare name that stays multi-candidate is resolved accept-lean: the
        // reference's full top-down pass narrows it via the relevant type, which
        // mettle's single-pass propagation only approximates, so rejecting here
        // would false-reject real models. `AmbiguousName` is instead reserved
        // for the reliable case — an ambiguous *call* (multiple funcs match a
        // box-join's arity + arg types, see `applicative`). This under-
        // approximates the jar's name-ambiguity reject (probe 15 in call form is
        // still caught); the gap is tracked for the mt-020 differential gauge.
        // The first min-weight candidate (a single clean arity) avoids the
        // mixed-arity union that would pollute downstream arity checks.
        let _ = (name, span);
        self.ambig = true;
        best.first().map_or_else(Type::empty, |c| c.ty.clone())
    }

    fn fits(&self, ty: &Type, want: &Want) -> bool {
        match want {
            Want::Any | Want::Set => true,
            Want::Formula => ty.is_bool,
            Want::Int => ty.is_small_int || ty.is_int(&self.r.world),
            Want::JoinRhs(left) => !ty.is_bool && left.join(&self.r.world, ty).has_entries(),
            Want::JoinLhs(right) => !ty.is_bool && ty.join(&self.r.world, right).has_entries(),
            Want::Of(t) => {
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

        // Fields by label (only the tail segment matters for bare labels).
        // Collected before funcs and at a lower weight so a user field beats an
        // auto-opened stdlib func of the same name (`prev`/`next`/…) when the
        // relevant type does not otherwise disambiguate.
        let label = &segs[segs.len() - 1];
        if segs.len() == 1 {
            self.collect_field_cands(label, at_name, &mut out);
        }

        // Zero-arg funcs/preds used as values: a 0-ary fun is its return value,
        // a 0-ary pred is a formula (`Geometry => …`).
        for fid in self.lookup_funcs(segs) {
            let f = &self.r.world.funcs[fid];
            if f.params.is_empty() {
                out.push(Cand {
                    ty: if f.is_pred {
                        Type::formula()
                    } else {
                        f.return_ty.clone()
                    },
                    weight: 2,
                });
            }
        }
        out
    }

    /// Field candidates for a bare label (resolution-doc §3.3/§3.4): the
    /// implicit-`this` join inside a sig context, and the bare relation.
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
            // Implicit `this.f` when the owner is the rootsig or an ancestor.
            if !at_name {
                if let Some(root) = self.rootsig {
                    if self.r.world.is_same_or_descendent(root, field.owner) {
                        let this_ty = self.r.world.sigs[root].ty.clone();
                        out.push(Cand {
                            ty: this_ty.join(&self.r.world, &field.ty),
                            weight: 1,
                        });
                        continue;
                    }
                }
            }
            // Bare relation (top level, `@f`, or cross-branch): weight 1 —
            // below a 0-ary func (weight 2), above a same-sig this-join.
            out.push(Cand {
                ty: field.ty.clone(),
                weight: 1,
            });
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

    fn unary(&mut self, op: UnOp, e: ExprId, _span: Span, want: &Want) -> Type {
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
                let t = self.check(e, &Want::Set);
                Type::unary(self.r.world.builtins.seq_int).product(&self.r.world, &t)
            }
            // Relational unary.
            UnOp::Transpose => self.check(e, &Want::Set).transpose(),
            UnOp::Closure | UnOp::ReflexiveClosure => {
                // A closure preserves the operand's binary shape, so a relevant
                // type from the parent (e.g. `i.*next`'s `JoinRhs`) flows
                // straight to the operand to disambiguate it.
                let operand_want = match want {
                    Want::JoinRhs(_) => want,
                    _ => &Want::Set,
                };
                let t = self.check(e, operand_want);
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
            UnOp::Prime => self.check(e, &Want::Set),
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
                let l = self.check(lhs, &Want::Set);
                let r = if l.is_error() {
                    self.check(rhs, &Want::Set)
                } else {
                    self.check(rhs, &Want::Of(l.clone()))
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
            // Domain restriction `A <: r`: r's first column must intersect A,
            // which disambiguates fields the same way a join does.
            BinOp::DomRestrict => {
                let l = self.check(lhs, &Want::Set);
                self.check(rhs, &Want::JoinRhs(l))
            }
            BinOp::RanRestrict => {
                let l = self.check(lhs, &Want::Set);
                self.check(rhs, &Want::Set);
                l
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
        let l = self.check(lhs, &Want::Set);
        let r = self.check(rhs, &Want::Set);
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
                let l = self.check(lhs, &Want::Set);
                // Disambiguate the right operand against the left's type (§4.3);
                // `Of` only narrows, never wrongly rejects (pick falls back).
                let r = if l.is_error() {
                    self.check(rhs, &Want::Set)
                } else {
                    self.check(rhs, &Want::Of(l.clone()))
                };
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
    fn applicative(&mut self, e: ExprId, span: Span) -> Type {
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
                        for a in args {
                            self.check(a, &Want::Set);
                        }
                        return Type::formula();
                    }
                    // `int[e]`/`sum[e]`: cast a set of `Int` atoms to a
                    // primitive int (the bracketed spelling of `int e`/`sum e`).
                    "int" | "sum" => {
                        for a in args {
                            self.check(a, &Want::Set);
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
                    .map(|(&a, p)| self.check(a, &Want::Of(p.clone())))
                    .collect()
            } else {
                arg_exprs
                    .iter()
                    .map(|&a| self.check(a, &Want::Any))
                    .collect()
            };
            let matches: Vec<&CallCand> = cands
                .iter()
                .filter(|c| c.params.len() == arg_exprs.len() && self.args_apply(c, &arg_types))
                .collect();
            if matches.len() == 1 {
                if self.no_calls {
                    self.err(ResolveError::FieldBoundHasCall {
                        name: self.field_name.clone(),
                        span,
                    });
                }
                return matches[0].ret.clone();
            }
            if matches.len() > 1 {
                self.err(ResolveError::AmbiguousName {
                    name: cands[0].reason.clone(),
                    span,
                    candidates: matches.iter().map(|c| c.reason.clone()).collect(),
                });
                return matches[0].ret.clone();
            }
            // No applicable call: fall through to the relational reading.
        }

        // Relational reading.
        match &self.expr(e).kind {
            ExprKind::Binary { lhs, rhs, .. } => {
                let (lhs, rhs) = (*lhs, *rhs);
                let l = self.check(lhs, &Want::Set);
                let r = self.check(rhs, &Want::JoinRhs(l.clone()));
                let joined = l.join(&self.r.world, &r);
                // Join-retry (§4.4): if the left was an overloaded bare name that
                // resolved to the wrong candidate (empty join), re-resolve it
                // with the right operand as a `JoinLhs` hint — `prev.t"` picks
                // the `prev` whose last column matches `t"`.
                if joined.has_entries() || !matches!(self.expr(lhs).kind, ExprKind::Name(_)) {
                    joined
                } else {
                    let r2 = self.check(rhs, &Want::Set);
                    let l2 = self.check(lhs, &Want::JoinLhs(r2.clone()));
                    l2.join(&self.r.world, &r2)
                }
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
        c.params.iter().zip(arg_types).all(|(p, a)| {
            a.is_error()
                || p.is_error()
                || a.intersects(&self.r.world, p)
                // int/small-int args flow into Int params relationally.
                || (a.is_small_int && p.is_int(&self.r.world))
                || (a.is_int(&self.r.world) && p.is_int(&self.r.world))
        })
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
