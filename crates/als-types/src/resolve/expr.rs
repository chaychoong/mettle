//! The expression type checker (resolution-doc §4) — the mt-025 **two-pass**
//! structure (ADR-0008 decision 4, finally built for real).
//!
//! The reference resolves an expression in two observable passes:
//!  1. **bottom-up `make`** builds a typed tree, attaching each node's bounding
//!     `Type` and any *make-time* error (arity/sort/`~^*`-non-binary/multiplicity),
//!     and turning ambiguous names/joins into `ExprChoice` candidate lists — the
//!     join distributes over an ambiguous right operand (`Context.process`), so
//!     `s.projects` becomes a *choice of joined results* `{s.(Person<:projects),
//!     s.(Course<:projects)}`, each carrying its own joined type;
//!  2. **top-down `resolve(relevantType)`** threads the precise relevant type
//!     down (the §4.3 per-op slices), picks each `ExprChoice` by
//!     `resolveHelper` against that relevant type (including the first-pass
//!     retry), and settles call-vs-join.
//!
//! mettle folds these into one recursive walk that (a) peeks each node's
//! bottom-up bounding type via the pure [`Cx::infer`] (so sibling slices are
//! exact), and (b) materializes the join/name **choice** locally and resolves it
//! against the **precise relevant [`Type`]** pushed from the parent — never the
//! lossy `Want` enum of mt-018/022. Because a choice resolves only its *chosen*
//! candidate, errors on discarded readings never surface: the accept/reject
//! verdict is exactly the reference's `errors.pick()` over the final resolved
//! tree, with **no** `ambig` / `join_lenient` / loose-want suppression (those
//! existed only because the fused walk lacked the parent's relevant type).
//!
//! No `int`↔`Int` coercion (resolution-doc §4.5). Candidate scope chain §4.4.

use als_syntax::ast::{
    BinOp, CmpOp, Const, Decl, DeclId, Expr, ExprId, ExprKind, LetBinding, QualName, Quant, UnOp,
};
use als_syntax::{ArenaId, Span};

use crate::choice::{
    BuiltinCall, BuiltinValue, CallChoice, ChoiceTable, ExprChoice, MacroChoice, NameChoice,
    SpineChoice,
};
use crate::error::ResolveError;
use crate::graph::ModuleId;
use crate::ty::Type;
use crate::warning::ResolveWarning;
use crate::world::{FieldId, FuncId, SigId};

use super::Resolver;

/// The result of resolving a node: its resolved bounding type, and whether the
/// subtree carried an error (the reference's `errors.isEmpty()` gate — a parent
/// suppresses its own make-error when a child already errored).
#[derive(Clone)]
struct R {
    ty: Type,
    err: bool,
}

impl R {
    fn ok(ty: Type) -> Self {
        R { ty, err: false }
    }
    fn bad() -> Self {
        R {
            ty: Type::empty(),
            err: true,
        }
    }
}

/// A value candidate for a bare name (resolution-doc §4.4 `populate`): a typed
/// leaf reading (sig / field-relation / implicit-`this` join / 0-ary call).
struct Cand {
    ty: Type,
    /// Disambiguation weight (implicit-`this`/cross-branch fields cost 1).
    weight: i32,
    /// Human-readable origin (the reference's `reasons`), for the ambiguity msg.
    reason: String,
    /// The resolved leaf (mt-031 choice recording): what this candidate *is*, so
    /// the winning candidate is recorded for the lowerer.
    origin: CandOrigin,
}

/// What a chosen name candidate resolves to, for choice recording (mt-031).
#[derive(Clone)]
enum CandOrigin {
    /// A signature.
    Sig(SigId),
    /// A field relation, with whether a standalone reference inserts implicit
    /// `this` (resolution-doc §3.3). Forced to `false` when the field is a join
    /// base (the join arg is the receiver).
    Field { field: FieldId, implicit_this: bool },
    /// A 0-ary func/pred inlined as a value.
    Call0(FuncId),
    /// A `fun/…` builtin value.
    Builtin(BuiltinValue),
    /// A lexically-bound variable.
    Var(String),
}

impl CandOrigin {
    /// The [`NameChoice`] this origin records. `join_base` forces a field's
    /// implicit `this` off (the join supplies the receiver).
    fn to_choice(&self, join_base: bool) -> NameChoice {
        match self {
            CandOrigin::Sig(s) => NameChoice::Sig(*s),
            CandOrigin::Field {
                field,
                implicit_this,
            } => NameChoice::Field {
                field: *field,
                implicit_this: *implicit_this && !join_base,
            },
            CandOrigin::Call0(f) => NameChoice::Call0(*f),
            CandOrigin::Builtin(b) => NameChoice::Builtin(*b),
            CandOrigin::Var(n) => NameChoice::Var(n.clone()),
        }
    }
}

/// One materialized reading of a join/application spine — a candidate in the
/// join-level `ExprChoice` (the reference's `Context.process` output).
#[derive(Clone)]
struct Reading {
    /// The reading's bottom-up (merged) result type.
    ty: Type,
    weight: i32,
    reason: String,
    fin: Fin,
    /// The `ExprId` of the spine's rightmost base (mt-031 choice recording).
    head_expr: ExprId,
    /// The base name's resolved leaf, when it is a name (recorded so the lowerer
    /// knows a join base's meaning without re-deriving §4.4).
    head_choice: Option<CandOrigin>,
}

/// How to *finalize* a chosen [`Reading`]: resolve its operands against the
/// slices derived from the relevant type, and emit any make-error.
#[derive(Clone)]
enum Fin {
    /// A leaf value already fully typed (sig/const/var/field-relation/this-join).
    Leaf,
    /// A relational join `left . right`: resolve `left` against the join
    /// left-slice; fire `IllegalJoin` if the join type is the `EMPTY` sentinel.
    /// `right_expr` is the compound right-operand expr when it is not a
    /// distributed name leaf (a field candidate needs no further resolution) —
    /// carried so its own warnings can be collected (a warning-only resolve that
    /// discards errors, so the verdict is unaffected; mt-023).
    Join {
        left: ExprId,
        right_ty: Type,
        right_expr: Option<ExprId>,
        span: Span,
        /// The recordable structure of the join base (mt-031 choice recording).
        base: Box<RecNode>,
    },
    /// A function/predicate call: resolve each arg against its parameter type.
    Call {
        func: FuncId,
        this_arg: Option<Type>,
        args: Vec<ExprId>,
        span: Span,
    },
    /// A pending / failed call spine (`ExprBadCall`, resolution-doc §4.4): the
    /// specific func, the args gathered so far, whether an implicit `this` is the
    /// first arg. If it survives resolution without completing, it is a reject.
    BadCall {
        func: FuncId,
        args: Vec<ExprId>,
        this_arg: bool,
        span: Span,
    },
    /// A parenthesized / compound right operand: resolve the whole sub-expr
    /// against the pushed relevant type.
    Sub(ExprId),
    /// A name with no candidate reading at all (unknown in a join/box spine):
    /// a reject unless the model is `$`-lenient.
    Unknown { name: String, span: Span },
}

/// The recordable structure of a join base (mt-031 choice recording): mirrors
/// the spine tree of the *winning* reading so [`Cx::flush_rec`] can record each
/// nested join node and base name without re-deriving §4.4.
#[derive(Clone)]
enum RecNode {
    /// A leaf base name resolved to `choice`, recorded at `expr`.
    Name {
        /// The base name's `ExprId`.
        expr: ExprId,
        /// Its resolved leaf.
        choice: CandOrigin,
    },
    /// A nested relational-join subspine node `expr` (join `arg . base`) whose
    /// base name(s) are `base` and whose argument operand is `arg`.
    Join {
        /// The nested spine node's `ExprId`.
        expr: ExprId,
        /// Its argument operand (the join left) — resolved standalone at flush to
        /// record its choices (it is never finalized in place, being buried as a
        /// base of the outer spine).
        arg: ExprId,
        /// Its base.
        base: Box<RecNode>,
    },
    /// A compound base (paren/closure/nested) resolved via the warning-only
    /// pass; its inner choices are recorded there, so nothing to flush here.
    Sub,
    /// Nothing to record here.
    Opaque,
}

/// The expression-typing context (see the module note). Borrows `&Resolver`
/// immutably; the caller harvests `errors`/`warnings` after the borrow ends.
pub(super) struct Cx<'a, 'g> {
    pub r: &'a Resolver<'g>,
    pub module: ModuleId,
    /// Lexical env (innermost binding last): let/quantifier vars, params, `this`.
    pub env: Vec<(String, Type)>,
    /// The enclosing sig, for implicit-`this` field resolution (§3.3).
    pub rootsig: Option<SigId>,
    /// A non-defined field bound: func/pred calls are disallowed (§3.4).
    pub no_calls: bool,
    /// The field label being bound (for the call-in-bound reject message).
    pub field_name: String,
    pub errors: Vec<ResolveError>,
    pub warnings: Vec<ResolveWarning>,
    /// Resolution choices recorded for the lowerer (mt-031), keyed by this
    /// context's [`Self::module`] and each node's `ExprId`.
    pub choices: ChoiceTable,
    /// Remaining macro-substitution budget (resolution-doc §3.7, starts at 20).
    unroll: u32,
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
            choices: ChoiceTable::new(),
            unroll: 20,
        }
    }

    // ---- choice recording (mt-031) ----

    /// Records a bare-name resolution at `(module, expr)`.
    fn record_name(&mut self, expr: ExprId, choice: NameChoice) {
        self.choices
            .record(self.module, expr, ExprChoice::Name(choice));
    }

    /// Records a spine (join/call/builtin/macro) resolution at `(module, expr)`.
    fn record_spine(&mut self, expr: ExprId, choice: SpineChoice) {
        self.choices
            .record(self.module, expr, ExprChoice::Spine(choice));
    }

    /// Walks the winning reading's base structure, recording each nested join
    /// node and base name (mt-031). `receiver` is the operand the base is joined
    /// onto (the join arg to its left), used to decide whether a sig-field base
    /// keeps its implicit `this` (see [`Self::field_base_uses_raw`]).
    fn flush_rec(&mut self, rec: &RecNode, receiver: Option<ExprId>) {
        match rec {
            RecNode::Name { expr, choice } => {
                let join_base = self.field_base_uses_raw(choice, receiver);
                let nc = choice.to_choice(join_base);
                self.record_name(*expr, nc);
            }
            RecNode::Join { expr, arg, base } => {
                self.record_spine(*expr, SpineChoice::Join);
                // The base is joined onto `arg` (`arg . base`), so `arg` is its
                // receiver for the implicit-`this` decision.
                self.flush_rec(base, Some(*arg));
                // The nested join's argument is never finalized in place (it is
                // buried as a base), so resolve it standalone to record its
                // choices — discarding any errors/warnings (verdict-neutral, the
                // node already resolved as part of the outer spine).
                self.record_operand(*arg);
            }
            RecNode::Sub | RecNode::Opaque => {}
        }
    }

    /// Whether a sig-field appearing as a join base uses the **raw** relation
    /// (implicit `this` stripped) rather than `this.field`.
    ///
    /// A field of the current sig only ever carries the implicit-`this`
    /// (`THIS.join(field)`) candidate (resolution-doc §3.3). When such a field is
    /// a join base `recv . field`, the receiver `recv` replaces `this` — but only
    /// when the **raw** relation actually joins with it, i.e. `recv`'s last column
    /// meets the field's owner column. That is the type-directed candidate choice
    /// `ExprChoice` makes (§4.4, min-weight prefers the penalty-free raw reading
    /// when it type-checks). When the raw join has no tuple (the receiver instead
    /// fills the field's declared domain, as in `holds[slot]` for a `State` field
    /// `holds`), implicit `this` is **kept** so the arg joins `this.field`.
    fn field_base_uses_raw(&self, choice: &CandOrigin, receiver: Option<ExprId>) -> bool {
        let CandOrigin::Field {
            implicit_this: true,
            field,
        } = choice
        else {
            // Non-field, or a field already without implicit `this`: unaffected
            // (`to_choice`'s `join_base` only touches an implicit-`this` field).
            return true;
        };
        let Some(recv) = receiver else {
            // A bare field base with no receiver keeps its implicit `this`.
            return false;
        };
        let recv_ty = self.infer(recv);
        let raw = &self.r.world.fields[*field].ty;
        recv_ty.join(&self.r.world, raw).has_tuple(&self.r.world)
    }

    /// Resolves `arg` against its own bottom-up type solely to **record** its
    /// resolution choices (mt-031), suppressing every error and warning so the
    /// accept/reject verdict and warning set stay byte-identical.
    fn record_operand(&mut self, arg: ExprId) {
        let nerr = self.errors.len();
        let nwarn = self.warnings.len();
        let p = self.infer(arg).remove_bool_and_int(self.int_sig());
        let _ = self.resolve(arg, &p);
        self.errors.truncate(nerr);
        self.warnings.truncate(nwarn);
    }

    /// The [`RecNode`] describing a base reading (its head name / nested join /
    /// compound sub-expr), for recording the winning spine.
    fn rec_of(reading: &Reading) -> RecNode {
        match &reading.fin {
            Fin::Leaf => match &reading.head_choice {
                Some(origin) => RecNode::Name {
                    expr: reading.head_expr,
                    choice: origin.clone(),
                },
                None => RecNode::Opaque,
            },
            Fin::Join { left, base, .. } => RecNode::Join {
                expr: reading.head_expr,
                arg: *left,
                base: base.clone(),
            },
            Fin::Sub(_) => RecNode::Sub,
            Fin::Call { .. } | Fin::BadCall { .. } | Fin::Unknown { .. } => RecNode::Opaque,
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

    /// Whether this model uses `$`-meta names anywhere (`sig$`/`field$`/
    /// `X$.subfields`). mettle does not synthesize the meta-sig atoms the meta
    /// phase would (resolution-doc §1 phase 8); it approximates them as `univ`,
    /// so an expression-level reject in a `$`-model may be an artifact of that
    /// approximation. The reference resolves these with real meta atoms, so
    /// mettle stays accept-lean (never rejects) in a `$`-model — the drop-in
    /// gate outranks the rare `$`-model over-acceptance (LIMITATIONS).
    fn lenient(&self) -> bool {
        self.r.graph.seen_dollar
    }

    fn int_sig(&self) -> SigId {
        self.r.world.builtins.int
    }

    #[allow(clippy::unused_self)]
    fn formula(&self) -> Type {
        Type::formula()
    }
    fn small_int(&self) -> Type {
        Type::small_int(self.int_sig())
    }

    // ---- public entry points (the three `resolve_as_*` wrappers, §4.3) ----

    /// `resolve_as_formula`: type-check `e` as a formula.
    pub(super) fn run_formula(&mut self, e: ExprId) {
        let p = self.formula();
        let mut r = self.resolve(e, &p);
        self.typecheck(&mut r, &p, self.expr(e).span);
    }

    /// `resolve_as_set`: type-check `e` as a relational value, returning its set
    /// type.
    pub(super) fn run_set(&mut self, e: ExprId) -> Type {
        // relevant = removesBoolAndInt(bottom-up type) (resolution-doc §4.3).
        let p = self.infer(e).remove_bool_and_int(self.int_sig());
        let mut r = self.resolve(e, &p);
        self.typecheck_as_set(&mut r, self.expr(e).span);
        r.ty.as_set(self.int_sig())
    }

    /// Resolves a declaration bound (field/param/quant): the relation type it
    /// denotes.
    pub(super) fn run_bound(&mut self, e: ExprId) -> Type {
        self.run_set(e)
    }

    // ================= bottom-up bounding types (pure `infer`) =================
    // Mirrors the reference's `.type` after `make`: no error/warning emission,
    // no choice resolution — an overloaded name yields the *merge* of its
    // candidate types (`ExprChoice.make`). Used to peek a sibling's type when
    // computing a child's precise relevant slice.

    fn infer(&self, e: ExprId) -> Type {
        let node = self.expr(e);
        match &node.kind {
            ExprKind::Num(_) => self.small_int(),
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
            ExprKind::Compare { .. } => self.formula(),
            ExprKind::IfThenElse {
                then_branch,
                else_branch,
                ..
            } => {
                let t = self.infer(*then_branch);
                let el = self.infer(*else_branch);
                if t.is_bool || el.is_bool {
                    self.formula()
                } else {
                    t.union(&self.r.world, &el)
                }
            }
            ExprKind::Quant { quant, .. } => {
                if matches!(quant, Quant::Sum) {
                    self.small_int()
                } else {
                    self.formula()
                }
            }
            ExprKind::Comprehension { decls, .. } => self.infer_comprehension(decls),
            ExprKind::Let { body, .. } => self.infer(*body),
            ExprKind::Block(exprs) => {
                if let [only] = exprs.as_slice() {
                    self.infer(*only)
                } else {
                    self.formula()
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

    fn infer_this(&self) -> Type {
        if let Some(t) = self.env_get("this") {
            return t;
        }
        self.rootsig.map_or_else(
            || Type::unary(self.r.world.builtins.univ),
            |s| self.r.world.sigs[s].ty.clone(),
        )
    }

    /// The bottom-up merge of a name's candidate types (no resolution).
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
        // A `this/tail` qualifier scopes to the CURRENT module's own decls
        // (getRawQS) — the merge over just those candidates.
        let raw: Vec<String> = qn.segments.iter().map(|s| s.text.clone()).collect();
        if raw.len() == 2 && raw[0] == "this" {
            let own = self.own_candidates(&raw[1], at_name);
            if !own.is_empty() {
                let mut merge = Type::empty();
                for c in &own {
                    merge = merge.merge(&self.r.world, &c.ty);
                }
                return merge;
            }
        }

        let cands = self.value_candidates(&segs, at_name);
        if cands.is_empty() {
            // A 0-param macro used as a value expands to its body type (needed so
            // `macro[x]` box joins the body relation, not a lenient `univ`).
            if let Some(t) = self.infer_zero_macro(&segs) {
                return t;
            }
            return Type::unary(self.r.world.builtins.univ);
        }
        let mut merge = Type::empty();
        for c in &cands {
            merge = merge.merge(&self.r.world, &c.ty);
        }
        merge
    }

    /// The body type of a 0-param macro (read-only, unroll-bounded), or `None`
    /// if `segs` is not a 0-param macro.
    fn infer_zero_macro(&self, segs: &[String]) -> Option<Type> {
        if self.unroll == 0 {
            return Some(Type::unary(self.r.world.builtins.univ));
        }
        let mid = self.lookup_macro(segs)?;
        if !self.r.world.macros[mid].params.is_empty() {
            return None;
        }
        let mac = self.r.world.macros[mid].clone();
        let mut sub = Cx::new(self.r, mac.module);
        sub.unroll = self.unroll - 1;
        sub.rootsig = self.rootsig;
        Some(sub.infer(mac.body))
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
            | UnOp::Once => self.formula(),
            UnOp::SetOf | UnOp::ExactlyOf => self.infer(e).remove_bool_and_int(world.builtins.int),
            UnOp::SomeOf | UnOp::LoneOf | UnOp::OneOf => self.infer(e).extract(world, 1),
            UnOp::SeqOf => Type::unary(world.builtins.seq_int).product(world, &self.infer(e)),
            UnOp::Transpose => self.infer(e).transpose(world),
            UnOp::Closure => self.infer(e).closure(world),
            UnOp::ReflexiveClosure => {
                Type::product_of(vec![world.builtins.univ, world.builtins.univ])
                    .union(world, &self.infer(e).closure(world))
            }
            UnOp::Card | UnOp::IntOf | UnOp::SumOf => self.small_int(),
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
            | BinOp::Seq => self.formula(),
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
            | BinOp::IntRem => self.small_int(),
        }
    }

    fn infer_comprehension(&self, decls: &[DeclId]) -> Type {
        let mut ty: Option<Type> = None;
        for &d in decls {
            let decl = &self.ast().decls[d];
            let bt = self.infer(decl.bound).remove_bool_and_int(self.int_sig());
            for _ in &decl.names {
                ty = Some(match ty {
                    None => bt.clone(),
                    Some(prev) => prev.product(&self.r.world, &bt),
                });
            }
        }
        ty.unwrap_or_else(Type::empty)
    }

    /// Bottom-up type of a `.`-join / box-join / call spine (no resolution).
    fn infer_applicative(&self, e: ExprId) -> Type {
        if let ExprKind::BoxJoin { target, args } = &self.expr(e).kind {
            if let ExprKind::Name(qn) = &self.expr(*target).kind {
                let joined = qn
                    .segments
                    .iter()
                    .map(|s| s.text.as_str())
                    .collect::<Vec<_>>()
                    .join("/");
                match joined.as_str() {
                    "pred/totalOrder" | "disj" => return self.formula(),
                    "int" | "sum" => return self.small_int(),
                    "Int" => return Type::unary(self.r.world.builtins.int),
                    _ => {}
                }
            }
            let _ = args;
        }
        if let Some((mid, _)) = self.collect_macro_spine(e) {
            let _ = mid;
            return Type::unary(self.r.world.builtins.univ);
        }
        // The bottom-up type is the **merge of all readings** (the reference's
        // `ExprChoice.make` merge) — a call reading contributes its return type
        // only when it is genuinely applicable (build_readings checks this), so a
        // non-applicable auto-opened pred (`integer/pos`) never poisons the type.
        let span = self.expr(e).span;
        let readings = self.build_readings(e, span);
        let mut merge = Type::empty();
        for r in &readings {
            merge = merge.merge(&self.r.world, &r.ty);
        }
        merge
    }

    // ==================== top-down resolve (Pass B) ====================

    /// Resolves `e` against the relevant type `p` (the reference's
    /// `Expr.resolve(t, warns)`), returning its resolved type and whether the
    /// subtree errored.
    fn resolve(&mut self, e: ExprId, p: &Type) -> R {
        let node = self.expr(e);
        let span = node.span;
        match &node.kind {
            ExprKind::Num(_) => R::ok(self.small_int()),
            ExprKind::Str(_) => R::ok(Type::unary(self.r.world.builtins.string)),
            ExprKind::Const(c) => R::ok(self.const_type(*c)),
            ExprKind::This => R::ok(self.infer_this()),
            ExprKind::Name(qn) => self.resolve_name(e, qn, p, false),
            ExprKind::AtName(qn) => self.resolve_name(e, qn, p, true),
            ExprKind::Unary { op, expr } => self.unary_r(*op, *expr, span, p),
            ExprKind::Binary {
                op: BinOp::Join, ..
            }
            | ExprKind::BoxJoin { .. } => self.applicative(e, span, p),
            ExprKind::Binary { op, lhs, rhs } => self.binary(*op, *lhs, *rhs, span, p),
            ExprKind::Arrow { lhs, rhs, .. } => self.arrow(*lhs, *rhs, span, p),
            ExprKind::Compare { op, lhs, rhs, .. } => self.compare(*op, *lhs, *rhs, span),
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self.if_then_else(*cond, *then_branch, *else_branch, p),
            ExprKind::Quant { quant, decls, body } => self.quant(*quant, decls, *body, span),
            ExprKind::Comprehension { decls, body } => self.comprehension(decls, *body),
            ExprKind::Let { bindings, body } => self.let_expr(bindings, *body, p),
            ExprKind::Block(exprs) => {
                if let [only] = exprs.as_slice() {
                    self.resolve(*only, p)
                } else {
                    // D (implicit conjunction): two juxtaposed formulas on the
                    // same source line, no explicit `and` (§5.2, `ExprList.makeAND`
                    // `pos == null && a.span().y2 == b.span().y`). Block elements
                    // are always the implicitly-conjoined case (`and`/`&&` build a
                    // Binary node, never a Block element). Position: between them.
                    for pair in exprs.windows(2) {
                        let (a, b) = (pair[0], pair[1]);
                        let (aspan, bspan) = (self.expr(a).span, self.expr(b).span);
                        if self.same_source_line(aspan.file, aspan.end, bspan.start) {
                            self.warnings.push(ResolveWarning::ImplicitConjunction {
                                span: Span::new(aspan.file, aspan.end, bspan.start),
                            });
                        }
                    }
                    let mut err = false;
                    for &f in exprs {
                        let fp = self.formula();
                        let mut r = self.resolve(f, &fp);
                        self.typecheck(&mut r, &fp, self.expr(f).span);
                        err |= r.err;
                    }
                    R {
                        ty: self.formula(),
                        err,
                    }
                }
            }
        }
    }

    /// `resolve` a child, then apply the reference's `typecheck_as_{formula,int,
    /// set}` for the position (make/`resolve_as_*` sort enforcement, §4.3).
    fn resolve_checked(&mut self, e: ExprId, p: &Type) -> R {
        let mut r = self.resolve(e, p);
        self.typecheck(&mut r, p, self.expr(e).span);
        r
    }

    /// The sort check for a relevant type `p` (formula / int / set), emitting
    /// `NotFormula`/`NotInt`/`NotSet` on mismatch. No cascade on an already-
    /// errored subtree (the reference's `errors.isEmpty()` short-circuit).
    fn typecheck(&mut self, r: &mut R, p: &Type, span: Span) {
        if r.err || self.lenient() {
            return;
        }
        if p.is_bool {
            if !r.ty.is_bool {
                self.err(ResolveError::NotFormula { span });
                r.err = true;
            }
        } else if p.is_small_int {
            if !r.ty.is_small_int && !r.ty.is_int(&self.r.world) {
                self.err(ResolveError::NotInt { span });
                r.err = true;
            }
        } else {
            self.typecheck_as_set(r, span);
        }
    }

    /// `typecheck_as_set`: a formula (`is_bool`) where a set is required is an
    /// error; a `small_int`/`is_int` is cast (no error). EMPTY is already an
    /// error subtree.
    fn typecheck_as_set(&mut self, r: &mut R, span: Span) {
        if r.err || self.lenient() {
            return;
        }
        if r.ty.is_bool {
            self.err(ResolveError::NotSet { span });
            r.err = true;
        }
    }

    // ---- operators (§4.3 slices) ----

    #[allow(clippy::too_many_lines)]
    fn unary_r(&mut self, op: UnOp, e: ExprId, span: Span, p: &Type) -> R {
        let world = &self.r.world;
        match op {
            UnOp::Not => {
                let fp = self.formula();
                let sub = self.resolve_checked(e, &fp);
                R {
                    ty: self.formula(),
                    err: sub.err,
                }
            }
            UnOp::No | UnOp::Some | UnOp::Lone | UnOp::One => {
                // relevant = removesBoolAndInt(sub.type)
                let s = self.infer(e).remove_bool_and_int(self.int_sig());
                let mut sub = self.resolve(e, &s);
                self.typecheck_as_set(&mut sub, self.expr(e).span);
                R {
                    ty: self.formula(),
                    err: sub.err,
                }
            }
            UnOp::SetOf | UnOp::ExactlyOf | UnOp::SomeOf | UnOp::LoneOf | UnOp::OneOf => {
                // multiplicity bound markers: operand as a set; result type per make.
                let s = self.infer(e).remove_bool_and_int(self.int_sig());
                let mut sub = self.resolve(e, &s);
                self.typecheck_as_set(&mut sub, self.expr(e).span);
                let ty = match op {
                    UnOp::SetOf | UnOp::ExactlyOf => sub.ty.remove_bool_and_int(self.int_sig()),
                    _ => sub.ty.extract(&self.r.world, 1),
                };
                if !sub.err && ty.is_error() && !self.lenient() {
                    // "After some/lone/one, this must be a unary set" / set-of / exactly-of.
                    self.err(ResolveError::NotSet { span });
                    return R::bad();
                }
                R { ty, err: sub.err }
            }
            UnOp::SeqOf => {
                let s = self.infer(e).remove_bool_and_int(self.int_sig());
                let mut sub = self.resolve(e, &s);
                self.typecheck_as_set(&mut sub, self.expr(e).span);
                R {
                    ty: Type::unary(self.r.world.builtins.seq_int).product(&self.r.world, &sub.ty),
                    err: sub.err,
                }
            }
            UnOp::Transpose => {
                // s = sub.type.transpose().intersect(p).transpose()
                let subt = self.infer(e);
                let s_pre = subt
                    .transpose(&self.r.world)
                    .intersect(&self.r.world, p)
                    .transpose(&self.r.world);
                // A2 (does not contribute): s == EMPTY && p.hasTuple() (§5.2).
                if s_pre.is_error() && p.has_tuple(&self.r.world) {
                    self.warnings.push(ResolveWarning::DoesNotContribute {
                        span: self.expr(e).span,
                    });
                }
                let s = if s_pre.has_entries() {
                    s_pre
                } else {
                    subt.clone()
                };
                let mut sub = self.resolve(e, &s);
                self.typecheck_as_set(&mut sub, self.expr(e).span);
                let ty = sub.ty.transpose(&self.r.world);
                if !sub.err && ty.is_error() && !self.lenient() {
                    self.err(ResolveError::UnaryNotBinary { op: "~", span });
                    return R::bad();
                }
                R { ty, err: sub.err }
            }
            UnOp::Closure | UnOp::ReflexiveClosure => {
                let subt = self.infer(e);
                // resolveClosure(p, sub.type) narrows the operand to its binary
                // part; mettle approximates with the operand's own binary shape
                // (closure-operand ambiguity is negligible for the verdict).
                let s = {
                    let c = subt.extract(&self.r.world, 2);
                    if c.has_entries() {
                        c
                    } else {
                        subt.clone()
                    }
                };
                let mut sub = self.resolve(e, &s);
                self.typecheck_as_set(&mut sub, self.expr(e).span);
                // Recording-only precise pass (mt-035): the operand type `s` above
                // is the operand's own binary shape, which leaves a bare `next`/
                // `prev` under `^`/`*` ambiguous between `util/ordering`'s
                // `elem->elem` and the auto-opened `util/integer`'s `Int->Int` — so
                // no choice is recorded and lowering an ordering model defers. When
                // this closure sits inside a join, the context relevant type `p`
                // carries the disambiguating binary shape (the reference's
                // `resolveClosure(p, sub.type)`). Re-resolve the operand against
                // `p`'s binary part purely to record the right leaf choice; discard
                // the type AND truncate errors + warnings so the accept/reject +
                // warning gauge stays byte-identical (invariance rule).
                let pbin = p.extract(&self.r.world, 2);
                if pbin.has_entries() {
                    let nerr = self.errors.len();
                    let nwarn = self.warnings.len();
                    let _ = self.resolve(e, &pbin);
                    self.errors.truncate(nerr);
                    self.warnings.truncate(nwarn);
                }
                let closed = sub.ty.closure(&self.r.world);
                if !sub.err && closed.is_error() && !self.lenient() {
                    self.err(ResolveError::UnaryNotBinary {
                        op: if matches!(op, UnOp::Closure) {
                            "^"
                        } else {
                            "*"
                        },
                        span,
                    });
                    return R::bad();
                }
                let ty = if matches!(op, UnOp::ReflexiveClosure) {
                    Type::product_of(vec![self.r.world.builtins.univ, self.r.world.builtins.univ])
                } else {
                    closed
                };
                // A1 (closure redundant): for `^` only, `this.type` joined with
                // itself has no tuple — domain and range are disjoint (§5.2). The
                // reference's `this.type` is the make-time (bottom-up) closure
                // type, not the relevant-narrowed `closed`.
                if matches!(op, UnOp::Closure) {
                    let bu = self.infer(e).closure(&self.r.world);
                    if bu.join(&self.r.world, &bu).has_no_tuple(&self.r.world) && bu.has_entries() {
                        self.warnings
                            .push(ResolveWarning::ClosureRedundant { span });
                    }
                }
                // A2 (does not contribute): the operand's relevant contribution
                // to the parent type is empty (`resolveClosure(p, sub.type) ==
                // EMPTY && p.hasTuple()`, §5.2). Computed on the bottom-up operand
                // type; used for the warning decision only (the *pushed* relevant
                // type is unchanged, so the verdict is untouched).
                let s_a2 = self.resolve_closure(p, &self.infer(e));
                if s_a2.is_error() && p.has_tuple(&self.r.world) {
                    self.warnings.push(ResolveWarning::DoesNotContribute {
                        span: self.expr(e).span,
                    });
                }
                R { ty, err: sub.err }
            }
            UnOp::Card => {
                let s = self.infer(e).remove_bool_and_int(self.int_sig());
                let mut sub = self.resolve(e, &s);
                self.typecheck_as_set(&mut sub, self.expr(e).span);
                R {
                    ty: self.small_int(),
                    err: sub.err,
                }
            }
            UnOp::IntOf | UnOp::SumOf => {
                // int[e]/sum e: cast a unary set of Int atoms to a primitive int.
                let subt = self.infer(e);
                // A5 (int atoms): the `int[]`/`sum` cast (CAST2INT), when the
                // operand can hold no Int atoms (§5.2). Position: the operand.
                if subt
                    .intersect(&self.r.world, &Type::unary(self.int_sig()))
                    .has_no_tuple(&self.r.world)
                {
                    self.warnings.push(ResolveWarning::IntAtoms {
                        span: self.expr(e).span,
                    });
                }
                let s = subt.remove_bool_and_int(self.int_sig());
                let mut sub = self.resolve(e, &s);
                self.typecheck_as_set(&mut sub, self.expr(e).span);
                R {
                    ty: self.small_int(),
                    err: sub.err,
                }
            }
            UnOp::Always
            | UnOp::Eventually
            | UnOp::After
            | UnOp::Before
            | UnOp::Historically
            | UnOp::Once => {
                let _ = world;
                let fp = self.formula();
                let sub = self.resolve_checked(e, &fp);
                R {
                    ty: self.formula(),
                    err: sub.err,
                }
            }
            UnOp::Prime => {
                // prime is a NOOP-typed postfix (§4.6): thread the parent relevant.
                self.resolve(e, p)
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn binary(&mut self, op: BinOp, lhs: ExprId, rhs: ExprId, span: Span, p: &Type) -> R {
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
            | BinOp::Seq => {
                let fp = self.formula();
                let l = self.resolve_checked(lhs, &fp);
                let r = self.resolve_checked(rhs, &fp);
                R {
                    ty: self.formula(),
                    err: l.err || r.err,
                }
            }
            BinOp::Join => unreachable!("join is handled by applicative"),
            BinOp::Union | BinOp::Override | BinOp::Intersect | BinOp::Diff => {
                let lt = self.infer(lhs);
                let rt = self.infer(rhs);
                // make-type + make-error (bottom-up), gated on children error-free.
                let (make_ty, arity_ok) = match op {
                    BinOp::Union | BinOp::Override => {
                        let t = lt.union_with_common_arity(world, &rt);
                        (t.clone(), t.has_entries())
                    }
                    BinOp::Intersect => {
                        let t = lt.intersect(world, &rt);
                        (t.clone(), t.has_entries())
                    }
                    BinOp::Diff => {
                        let t = lt.pick_common_arity(world, &rt);
                        (t.clone(), t.has_entries())
                    }
                    _ => unreachable!(),
                };
                // relevant slices (§4.3): +/++/& = a.intersect(p),b.intersect(p);
                // - = a=p, b=p.intersect(b).
                let (ap, bp) = match op {
                    BinOp::Diff => (p.clone(), p.intersect(world, &rt)),
                    _ => (lt.intersect(world, p), rt.intersect(world, p)),
                };
                let l = self.resolve_checked(lhs, &ap);
                let r = self.resolve_checked(rhs, &bp);
                if !l.err && !r.err && !arity_ok && !self.lenient() {
                    self.err(ResolveError::ArityMismatch {
                        op: bin_sym(op),
                        span,
                    });
                    return R::bad();
                }
                // Relevance/redundancy warnings (§5.2 A6/A7/A8), on a well-typed
                // node whose children resolved cleanly.
                if !l.err && !r.err {
                    match op {
                        // A6: `&` — the intersection type is statically empty.
                        BinOp::Intersect if make_ty.has_no_tuple(world) => {
                            self.warnings
                                .push(ResolveWarning::IntersectIrrelevant { span });
                        }
                        // A7: `+`/`++` — a side contributes nothing to `p`.
                        BinOp::Union | BinOp::Override if ap.is_error() || bp.is_error() => {
                            self.warnings.push(ResolveWarning::PlusIrrelevant { span });
                        }
                        // A8: `-` — the result or the narrowed right side is empty.
                        BinOp::Diff if make_ty.has_no_tuple(world) || bp.has_no_tuple(world) => {
                            self.warnings.push(ResolveWarning::MinusIrrelevant { span });
                        }
                        _ => {}
                    }
                }
                let ty = match op {
                    BinOp::Diff => lt.pick_common_arity(world, &rt),
                    _ => make_ty,
                };
                R {
                    ty,
                    err: l.err || r.err,
                }
            }
            BinOp::DomRestrict => {
                let lt = self.infer(lhs);
                let rt = self.infer(rhs);
                let make_ty = rt.domain_restrict(world, &lt);
                let (ap, bp) = self.domain_slices(&lt, &rt, p);
                let l = self.resolve_checked(lhs, &ap);
                let r = self.resolve_checked(rhs, &bp);
                if !l.err && !r.err && make_ty.is_error() && !self.lenient() {
                    self.err(ResolveError::NotUnarySet {
                        span: self.expr(lhs).span,
                    });
                    return R::bad();
                }
                // A10: `<:` result is always empty (§5.2).
                if !l.err && !r.err && make_ty.has_no_tuple(world) {
                    self.warnings
                        .push(ResolveWarning::DomainIrrelevant { span });
                }
                R {
                    ty: make_ty,
                    err: l.err || r.err,
                }
            }
            BinOp::RanRestrict => {
                let lt = self.infer(lhs);
                let rt = self.infer(rhs);
                let make_ty = lt.range_restrict(world, &rt);
                let (ap, bp) = self.range_slices(&lt, &rt, p);
                let l = self.resolve_checked(lhs, &ap);
                let r = self.resolve_checked(rhs, &bp);
                if !l.err && !r.err && make_ty.is_error() && !self.lenient() {
                    self.err(ResolveError::NotUnarySet {
                        span: self.expr(rhs).span,
                    });
                    return R::bad();
                }
                // A11: `:>` result is always empty (§5.2).
                if !l.err && !r.err && make_ty.has_no_tuple(world) {
                    self.warnings.push(ResolveWarning::RangeIrrelevant { span });
                }
                R {
                    ty: make_ty,
                    err: l.err || r.err,
                }
            }
            BinOp::Shl
            | BinOp::Sha
            | BinOp::Shr
            | BinOp::IntAdd
            | BinOp::IntSub
            | BinOp::IntMul
            | BinOp::IntDiv
            | BinOp::IntRem => {
                let ip = self.small_int();
                let l = self.resolve_checked(lhs, &ip);
                let r = self.resolve_checked(rhs, &ip);
                R {
                    ty: self.small_int(),
                    err: l.err || r.err,
                }
            }
        }
    }

    fn arrow(&mut self, lhs: ExprId, rhs: ExprId, span: Span, p: &Type) -> R {
        let world = &self.r.world;
        let lt = self.infer(lhs);
        let rt = self.infer(rhs);
        // Arrow slices: leftType' from p.intersect(aa.product(bb)); fallback a=a,b=b.
        let (ap, bp) = self.arrow_slices(&lt, &rt, p);
        let l = self.resolve_checked(lhs, &ap);
        let r = self.resolve_checked(rhs, &bp);
        // A12: one side of `->` is empty while the other is not (§5.2 default).
        if !l.err && !r.err {
            let lt_tuple = lt.has_tuple(world);
            let rt_tuple = rt.has_tuple(world);
            if lt_tuple != rt_tuple {
                self.warnings.push(ResolveWarning::ArrowIrrelevant { span });
            }
        }
        R {
            ty: lt.product(world, &rt),
            err: l.err || r.err,
        }
    }

    /// The `->` (default) resolve slice: `leftType' = {r1 | ∃ r2, r1->r2 ∈ p}`,
    /// `rightType' = {r2 | ∃ r1, r1->r2 ∈ p}`, with the reference's fallback to
    /// the raw operand types when either slice empties.
    fn arrow_slices(&self, a: &Type, b: &Type, p: &Type) -> (Type, Type) {
        let world = &self.r.world;
        let mut left = Type::empty();
        let mut right = Type::empty();
        for aa in &a.entries {
            if aa.is_empty(world) {
                continue;
            }
            for bb in &b.entries {
                if bb.is_empty(world) {
                    continue;
                }
                let prod =
                    Type::product_of(aa.0.clone()).product(world, &Type::product_of(bb.0.clone()));
                let inter = p.intersect(world, &prod);
                for cc in &inter.entries {
                    if cc.is_empty(world) {
                        continue;
                    }
                    let al = cc.0[..aa.arity()].to_vec();
                    let ar = cc.0[aa.arity()..].to_vec();
                    left = left.union(world, &Type::product_of(al));
                    right = right.union(world, &Type::product_of(ar));
                }
            }
        }
        if left.is_error() || right.is_error() {
            (a.clone(), b.clone())
        } else {
            (left, right)
        }
    }

    /// The `<:` DOMAIN resolve slice (resolution-doc §4.3): the left (domain)
    /// operand is restricted to the unary parts that survive `p`, the right to
    /// the relations whose first column those unaries restrict.
    #[allow(clippy::many_single_char_names)]
    fn domain_slices(&self, a: &Type, b: &Type, p: &Type) -> (Type, Type) {
        let world = &self.r.world;
        let mut left = Type::empty();
        let mut right = Type::empty();
        for aa in &a.entries {
            if aa.arity() != 1 {
                continue;
            }
            for bb in &b.entries {
                if !p.has_arity(bb.arity()) {
                    continue;
                }
                let restricted = restrict_col(world, bb, aa.0[0], 0);
                let inter = p.intersect(world, &Type::product_of(restricted.0));
                for cc in &inter.entries {
                    if cc.is_empty(world) {
                        continue;
                    }
                    left = left.union(world, &Type::product_of(vec![cc.0[0]]));
                    right = right.union(world, &Type::product_of(cc.0.clone()));
                }
            }
        }
        if left.is_error() || right.is_error() {
            let l = a.extract(world, 1);
            let r = b.pick_common_arity(world, p);
            (
                if l.has_entries() { l } else { a.clone() },
                if r.has_entries() { r } else { b.clone() },
            )
        } else {
            (left, right)
        }
    }

    /// The `:>` RANGE resolve slice (resolution-doc §4.3), symmetric to
    /// [`Self::domain_slices`] on the last column.
    #[allow(clippy::many_single_char_names)]
    fn range_slices(&self, a: &Type, b: &Type, p: &Type) -> (Type, Type) {
        let world = &self.r.world;
        let mut left = Type::empty();
        let mut right = Type::empty();
        for bb in &b.entries {
            if bb.arity() != 1 {
                continue;
            }
            for aa in &a.entries {
                if !p.has_arity(aa.arity()) {
                    continue;
                }
                let restricted = restrict_col(world, aa, bb.0[0], aa.arity() - 1);
                let inter = p.intersect(world, &Type::product_of(restricted.0));
                for cc in &inter.entries {
                    if cc.is_empty(world) {
                        continue;
                    }
                    left = left.union(world, &Type::product_of(cc.0.clone()));
                    let last = cc.arity() - 1;
                    right = right.union(world, &Type::product_of(vec![cc.0[last]]));
                }
            }
        }
        if left.is_error() || right.is_error() {
            let l = a.pick_common_arity(world, p);
            let r = b.extract(world, 1);
            (
                if l.has_entries() { l } else { a.clone() },
                if r.has_entries() { r } else { b.clone() },
            )
        } else {
            (left, right)
        }
    }

    fn compare(&mut self, op: CmpOp, lhs: ExprId, rhs: ExprId, span: Span) -> R {
        let world = &self.r.world;
        match op {
            CmpOp::Lt | CmpOp::Gt | CmpOp::Le | CmpOp::Ge => {
                let ip = self.small_int();
                let l = self.resolve_checked(lhs, &ip);
                let r = self.resolve_checked(rhs, &ip);
                R {
                    ty: self.formula(),
                    err: l.err || r.err,
                }
            }
            CmpOp::Eq | CmpOp::In => {
                let lt = self.infer(lhs);
                let rt = self.infer(rhs);
                let (ap, bp) = if matches!(op, CmpOp::Eq) {
                    // = : p=a.intersect(b); if p.hasTuple a=b=p else a=a.pickCommonArity(b),b=b.pickCommonArity(a)
                    let pp = lt.intersect(world, &rt);
                    if pp.has_tuple(world) {
                        (pp.clone(), pp)
                    } else {
                        (
                            lt.pick_common_arity(world, &rt),
                            rt.pick_common_arity(world, &lt),
                        )
                    }
                } else {
                    // in : a=a.pickCommonArity(b); b=b.intersect(a)
                    let a = lt.pick_common_arity(world, &rt);
                    let b = rt.intersect(world, &a);
                    (a, b)
                };
                let l = self.resolve_checked(lhs, &ap);
                let r = self.resolve_checked(rhs, &bp);
                let both_int = lt.is_int(world) && rt.is_int(world);
                let arity_ok = lt.has_common_arity(&rt) || (matches!(op, CmpOp::Eq) && both_int);
                if !l.err && !r.err && !arity_ok && !self.lenient() {
                    self.err(ResolveError::ArityMismatch {
                        op: if matches!(op, CmpOp::Eq) { "=" } else { "in" },
                        span,
                    });
                    return R::bad();
                }
                // Redundancy warnings (§5.2 A3/A4) on a well-typed comparison.
                if !l.err && !r.err {
                    // "Same value" mirrors the reference's structural
                    // `ExprBinary.isSame`. (Rare divergence: the reference's
                    // isSame fails to fire on `+`/`-` compounds over a *var field*
                    // — e.g. `(A->B - f) + f = …` — for temporal-resolution
                    // reasons; mettle's structural check fires, a documented
                    // handful of mettle-EXTRA, warning-parity.md.)
                    let same = self.same_expr(lhs, rhs);
                    match op {
                        // A3: `=`/`!=` sides always disjoint or always identical.
                        CmpOp::Eq
                            if (lt.has_tuple(world)
                                && rt.has_tuple(world)
                                && !lt.intersects(world, &rt))
                                || same =>
                        {
                            self.warnings.push(ResolveWarning::EqRedundant { span });
                        }
                        // A4: `in`/`!in` — a side empty, disjoint, or identical.
                        CmpOp::In
                            if lt.has_no_tuple(world)
                                || rt.has_no_tuple(world)
                                || bp.has_no_tuple(world)
                                || same =>
                        {
                            self.warnings.push(ResolveWarning::SubsetRedundant { span });
                        }
                        _ => {}
                    }
                }
                R {
                    ty: self.formula(),
                    err: l.err || r.err,
                }
            }
        }
    }

    fn if_then_else(&mut self, cond: ExprId, then_e: ExprId, else_e: ExprId, p: &Type) -> R {
        let world = &self.r.world;
        let fp = self.formula();
        let c = self.resolve_checked(cond, &fp);
        // ITE slice: if p.size>0 a=a.intersect(p),b=b.intersect(p) else a=b=p.
        let (ap, bp) = if p.has_entries() || p.is_bool || p.is_small_int {
            let at = self.infer(then_e);
            let bt = self.infer(else_e);
            let ap = at.intersect(world, p);
            let bp = bt.intersect(world, p);
            // C (redundant ITE branch): when the parent relevant type has
            // entries, a branch whose type had tuples but whose narrowed type
            // does not is redundant (§5.2). Positions: the branch expressions.
            if p.has_entries() && !p.is_bool {
                if at.has_tuple(world) && !ap.has_tuple(world) {
                    self.warnings.push(ResolveWarning::RedundantIteBranch {
                        span: self.expr(then_e).span,
                    });
                }
                if bt.has_tuple(world) && !bp.has_tuple(world) {
                    self.warnings.push(ResolveWarning::RedundantIteBranch {
                        span: self.expr(else_e).span,
                    });
                }
            }
            (ap, bp)
        } else {
            (p.clone(), p.clone())
        };
        // makeBool when p.is_bool: push formula relevant.
        let (ap, bp) = if p.is_bool {
            (self.formula(), self.formula())
        } else {
            (ap, bp)
        };
        let t = self.resolve_checked(then_e, &ap);
        let el = self.resolve_checked(else_e, &bp);
        let ty = if t.ty.is_bool || el.ty.is_bool {
            self.formula()
        } else {
            t.ty.union(world, &el.ty)
        };
        R {
            ty,
            err: c.err || t.err || el.err,
        }
    }

    // ---- names & candidates (§4.4) ----

    fn resolve_name(&mut self, e: ExprId, qn: &QualName, p: &Type, at_name: bool) -> R {
        let segs = super::strip_this(qn.segments.iter().map(|s| s.text.clone()).collect());

        if !at_name && segs.len() == 1 {
            if let Some(t) = self.env_get(&segs[0]) {
                self.record_name(e, NameChoice::Var(segs[0].clone()));
                return R::ok(t);
            }
        }
        if let Some(t) = self.builtin_value(&segs) {
            if let Some(bv) = builtin_value_choice(&segs) {
                self.record_name(e, NameChoice::Builtin(bv));
            }
            return R::ok(t);
        }
        if let Some(mid) = self.lookup_macro(&segs) {
            if self.r.world.macros[mid].params.is_empty() {
                return self.expand_macro(e, mid, &[], p);
            }
        }

        // A `this/tail` qualifier scopes to the CURRENT module's own decls first
        // (getRawQS): if `tail` is declared here, only those candidates are used
        // (never the auto-opened `util/integer` overloads) — the reference's rule
        // that makes `~this/next` unambiguous where `~next` is ambiguous.
        let raw: Vec<String> = qn.segments.iter().map(|s| s.text.clone()).collect();
        if raw.len() == 2 && raw[0] == "this" {
            let own = self.own_candidates(&raw[1], at_name);
            if !own.is_empty() {
                return self.pick_name(e, &own, p, &raw[1], qn.span);
            }
        }

        let cands = self.value_candidates(&segs, at_name);
        if cands.is_empty() {
            if !self.lookup_funcs(&segs).is_empty() || self.lookup_macro(&segs).is_some() {
                return R::ok(Type::unary(self.r.world.builtins.univ));
            }
            if segs.iter().any(|s| s.contains('$')) || self.r.graph.seen_dollar {
                return R::ok(Type::unary(self.r.world.builtins.univ));
            }
            self.err(ResolveError::UnknownName {
                name: segs.join("/"),
                span: qn.span,
            });
            return R::bad();
        }
        // resolveHelper over the leaf candidates against p.
        self.pick_name(e, &cands, p, &segs.join("/"), qn.span)
    }

    /// `ExprChoice.resolveHelper` over leaf name candidates (§4.4), on precise
    /// types (mt-022/025). Returns the resolved type, or an ambiguity/no-match
    /// reject at a definite position.
    fn pick_name(&mut self, e: ExprId, cands: &[Cand], p: &Type, name: &str, span: Span) -> R {
        if let [only] = cands {
            let nc = only.origin.to_choice(false);
            self.record_name(e, nc);
            return R::ok(only.ty.clone());
        }
        let types: Vec<Type> = cands.iter().map(|c| c.ty.clone()).collect();
        let weights: Vec<i32> = cands.iter().map(|c| c.weight).collect();
        match self.resolve_helper(&types, &weights, p) {
            Pick::One(i) => {
                let nc = cands[i].origin.to_choice(false);
                self.record_name(e, nc);
                R::ok(cands[i].ty.clone())
            }
            Pick::NoneArity(k) => {
                self.record_name(e, NameChoice::EmptyArity(k));
                R::ok(self.none_of_arity(k))
            }
            Pick::Ambiguous(idxs) => {
                if self.lenient() {
                    return R::ok(cands[idxs[0]].ty.clone());
                }
                self.err(ResolveError::AmbiguousName {
                    name: name.to_owned(),
                    span,
                    candidates: idxs.iter().map(|&i| cands[i].reason.clone()).collect(),
                });
                R::bad()
            }
            Pick::NoIntersect => {
                if self.lenient() {
                    return R::ok(cands[0].ty.clone());
                }
                self.err(ResolveError::AmbiguousName {
                    name: name.to_owned(),
                    span,
                    candidates: cands.iter().map(|c| c.reason.clone()).collect(),
                });
                R::bad()
            }
        }
    }

    /// The reference `ExprChoice.resolveHelper` (resolution-doc §4.4) over a
    /// candidate type list. Leaf candidates (mettle's readings are pre-typed) so
    /// the first-pass retry is a fixpoint — implemented as the same min-weight
    /// selection.
    fn resolve_helper(&self, types: &[Type], weights: &[i32], p: &Type) -> Pick {
        let world = &self.r.world;
        // exact matches: (p.is_bool && c.is_bool) || p.intersects(c).
        let mut pool: Vec<usize> = (0..types.len())
            .filter(|&i| (p.is_bool && types[i].is_bool) || p.intersects(world, &types[i]))
            .collect();
        // else legal matches: c.hasCommonArity(p).
        if pool.is_empty() {
            pool = (0..types.len())
                .filter(|&i| types[i].has_common_arity(p))
                .collect();
        }
        if pool.is_empty() {
            return Pick::NoIntersect;
        }
        // min-weight survivors.
        if pool.len() > 1 {
            let minw = pool.iter().map(|&i| weights[i]).min().unwrap_or(0);
            pool.retain(|&i| weights[i] == minw);
        }
        if pool.len() == 1 {
            return Pick::One(pool[0]);
        }
        // >1 but all collapse to the same-arity empty set → none of that arity.
        let mut arity: Option<usize> = None;
        let mut collapse = true;
        for &i in &pool {
            let t = &types[i];
            if t.is_bool || t.is_small_int || t.is_int(world) || t.has_tuple(world) {
                collapse = false;
                break;
            }
            match t.arity() {
                Some(a) if a >= 1 => {
                    if let Some(prev) = arity {
                        if prev != a {
                            collapse = false;
                            break;
                        }
                    } else {
                        arity = Some(a);
                    }
                }
                _ => {
                    collapse = false;
                    break;
                }
            }
        }
        if collapse {
            if let Some(a) = arity {
                return Pick::NoneArity(a);
            }
        }
        Pick::Ambiguous(pool)
    }

    fn none_of_arity(&self, k: usize) -> Type {
        let none = self.r.world.builtins.none;
        Type::product_of(vec![none; k.max(1)])
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

    /// Expands a macro by textual substitution (resolution-doc §3.7), recording
    /// a replay record at the call-site node `e` (mt-031): the macro, its args,
    /// and the body's choices resolved *for this site* (a nested table, since
    /// the same body `ExprId` may resolve differently per call).
    fn expand_macro(
        &mut self,
        e: ExprId,
        mid: crate::world::MacroId,
        arg_exprs: &[ExprId],
        p: &Type,
    ) -> R {
        if self.unroll == 0 {
            self.err(ResolveError::MacroTooDeep {
                span: self.r.world.macros[mid].span,
            });
            return R::ok(Type::unary(self.r.world.builtins.univ));
        }
        let arg_types: Vec<Type> = arg_exprs
            .iter()
            .map(|&a| {
                let ap = self.infer(a);
                self.resolve(a, &ap).ty
            })
            .collect();
        // A macro receiving a *callable passed by name* (`interesting_not_axiom
        // [Hb_p]`) cannot be faithfully typed by mettle's type-only param
        // binding — the reference substitutes the name textually so `param[args]`
        // in the body becomes a real call. Resolve such a body **accept-lean**
        // (drop its errors), so the approximation never wrongly rejects (mt-020).
        let lean = arg_exprs.iter().any(|&a| self.arg_is_callable_by_name(a));
        let mac = self.r.world.macros[mid].clone();
        let mut sub = Cx::new(self.r, mac.module);
        sub.unroll = self.unroll - 1;
        sub.rootsig = self.rootsig;
        for (name, ty) in mac.params.iter().zip(&arg_types) {
            sub.env.push((name.clone(), ty.clone()));
        }
        let mut r = sub.resolve(mac.body, p);
        // Record the replay (mt-031): a `Name` node (0-param macro used as a
        // value) records a `NameChoice::Macro`; a spine node a `SpineChoice`.
        let mc = MacroChoice {
            macro_id: mid,
            body_module: mac.module,
            args: arg_exprs.to_vec(),
            arg_module: self.module,
            body_choices: Box::new(std::mem::take(&mut sub.choices)),
            lean,
        };
        if matches!(self.expr(e).kind, ExprKind::Name(_) | ExprKind::AtName(_)) {
            self.record_name(e, NameChoice::Macro(mc));
        } else {
            self.record_spine(e, SpineChoice::Macro(mc));
        }
        if lean {
            // Accept-lean: drop the body's errors AND mark the result errored so
            // the *caller's* sort/typecheck never rejects either (a higher-order
            // macro's expanded `param[args]` type is only approximated).
            r.err = true;
        } else {
            self.errors.append(&mut sub.errors);
        }
        self.warnings.append(&mut sub.warnings);
        r
    }

    /// Whether `e` is a bare name referring to a func/pred/macro that *takes
    /// arguments* — a callable passed by name, with no 0-ary value reading.
    fn arg_is_callable_by_name(&self, e: ExprId) -> bool {
        let ExprKind::Name(qn) = &self.expr(e).kind else {
            return false;
        };
        let segs = super::strip_this(qn.segments.iter().map(|s| s.text.clone()).collect());
        if segs.len() == 1 && self.env_get(&segs[0]).is_some() {
            return false;
        }
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

    /// Builtin value names: `fun/max`, `fun/min`, `fun/next`, `fun/prev` (§4.5).
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
        if let Some(sig) = self.r.lookup_sig_from(self.module, segs) {
            out.push(Cand {
                ty: self.r.world.sigs[sig].ty.clone(),
                weight: 0,
                reason: format!("sig {}", self.r.world.sigs[sig].name),
                origin: CandOrigin::Sig(sig),
            });
        }
        for fid in self.lookup_funcs(segs) {
            let f = &self.r.world.funcs[fid];
            if f.params.is_empty() {
                out.push(Cand {
                    ty: if f.is_pred {
                        self.formula()
                    } else {
                        f.return_ty.clone()
                    },
                    weight: 0,
                    reason: format!("{} {}", if f.is_pred { "pred" } else { "fun" }, f.name),
                    origin: CandOrigin::Call0(fid),
                });
            }
        }
        let label = &segs[segs.len() - 1];
        if segs.len() == 1 {
            self.collect_field_cands(label, at_name, &mut out);
        }
        out
    }

    /// Candidates for a `this/tail` name: sigs/0-ary funcs/fields declared in
    /// the **current module only** (the reference's `getRawQS` own-module scope).
    fn own_candidates(&self, tail: &str, at_name: bool) -> Vec<Cand> {
        let mut out = Vec::new();
        let m = &self.r.mods[self.module.index()];
        if let Some(&sig) = m.sigs.get(tail).or_else(|| m.param_sigs.get(tail)) {
            out.push(Cand {
                ty: self.r.world.sigs[sig].ty.clone(),
                weight: 0,
                reason: format!("sig {}", self.r.world.sigs[sig].name),
                origin: CandOrigin::Sig(sig),
            });
        }
        if let Some(fids) = m.funcs.get(tail) {
            for &fid in fids {
                let f = &self.r.world.funcs[fid];
                if f.params.is_empty() {
                    out.push(Cand {
                        ty: if f.is_pred {
                            self.formula()
                        } else {
                            f.return_ty.clone()
                        },
                        weight: 0,
                        reason: format!("{} {}", if f.is_pred { "pred" } else { "fun" }, f.name),
                        origin: CandOrigin::Call0(fid),
                    });
                }
            }
        }
        // Fields owned by a sig declared in this module.
        for (fid, field) in self.r.world.fields.iter() {
            if field.name != tail || self.r.world.sigs[field.owner].module != self.module {
                continue;
            }
            self.push_field_cand(fid, field, at_name, &mut out);
        }
        out
    }

    /// Field candidates for a bare label (resolution-doc §3.3/§3.4, weights per
    /// `populate` resolution-mode 1).
    fn collect_field_cands(&self, label: &str, at_name: bool, out: &mut Vec<Cand>) {
        for (fid, field) in self.r.world.fields.iter() {
            if field.name != *label {
                continue;
            }
            let owner_mod = self.r.world.sigs[field.owner].module;
            if !self.reachable_contains(owner_mod) {
                continue;
            }
            self.push_field_cand(fid, field, at_name, out);
        }
    }

    /// Pushes the candidate reading(s) for one field per `populate` (weights per
    /// resolution-mode 1: implicit-`this`/bare 0, cross-branch 1).
    fn push_field_cand(
        &self,
        fid: FieldId,
        field: &crate::world::ResolvedField,
        at_name: bool,
        out: &mut Vec<Cand>,
    ) {
        let reason = format!(
            "field {} <: {}",
            self.r.world.sigs[field.owner].name, field.name
        );
        // implicit `this` is inserted only for a bare (non-`@`) reference in a
        // sig context whose `this` descends from the field owner (§3.3).
        let implicit_this = match self.rootsig {
            Some(root) => !at_name && self.r.world.sig_is_same_or_descendent(root, field.owner),
            None => false,
        };
        let origin = CandOrigin::Field {
            field: fid,
            implicit_this,
        };
        match self.rootsig {
            None => out.push(Cand {
                ty: field.ty.clone(),
                weight: 0,
                reason,
                origin,
            }),
            Some(root) if self.r.world.sig_is_same_or_descendent(root, field.owner) => {
                if at_name {
                    out.push(Cand {
                        ty: field.ty.clone(),
                        weight: 0,
                        reason,
                        origin,
                    });
                } else {
                    let this_ty = self.r.world.sigs[root].ty.clone();
                    out.push(Cand {
                        ty: this_ty.join(&self.r.world, &field.ty),
                        weight: 0,
                        reason,
                        origin,
                    });
                }
            }
            Some(_) => out.push(Cand {
                ty: field.ty.clone(),
                weight: 1,
                reason,
                origin,
            }),
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

    // ---- application vs relational join (§4.4) — the materialized join choice ----

    /// Resolves a `.`-join or box-join node by building the join-level
    /// `ExprChoice` (the reference's `Context.process`) and picking against the
    /// precise relevant type `p` (`resolveHelper`).
    #[allow(clippy::too_many_lines)]
    fn applicative(&mut self, e: ExprId, span: Span, p: &Type) -> R {
        // Builtin box-join targets.
        if let ExprKind::BoxJoin { target, args } = &self.expr(e).kind {
            if let ExprKind::Name(qn) = &self.expr(*target).kind {
                let joined = qn
                    .segments
                    .iter()
                    .map(|s| s.text.as_str())
                    .collect::<Vec<_>>()
                    .join("/");
                let args = args.clone();
                match joined.as_str() {
                    "pred/totalOrder" => {
                        // ExprList TOTALORDER: t = args[0].pickUnary(); args[0],
                        // args[1] resolve against t; args[2] against t.product(t).
                        let mut err = false;
                        let t = if let Some(&a0) = args.first() {
                            self.infer(a0).extract(&self.r.world, 1)
                        } else {
                            Type::empty()
                        };
                        let tt = t.product(&self.r.world, &t);
                        for (i, a) in args.iter().enumerate() {
                            let ap = if i >= 2 { &tt } else { &t };
                            let mut r = self.resolve(*a, ap);
                            self.typecheck_as_set(&mut r, self.expr(*a).span);
                            err |= r.err;
                        }
                        self.record_spine(
                            e,
                            SpineChoice::Builtin {
                                op: BuiltinCall::TotalOrder,
                            },
                        );
                        return R {
                            ty: self.formula(),
                            err,
                        };
                    }
                    "disj" => {
                        // ExprList DISJOINT: p = removesBoolAndInt(a0); then
                        // p = p.unionWithCommonArity(ai); each arg resolves vs p.
                        let mut p = Type::empty();
                        for (i, a) in args.iter().enumerate() {
                            let at = self.infer(*a);
                            p = if i == 0 {
                                at.remove_bool_and_int(self.int_sig())
                            } else {
                                p.union_with_common_arity(&self.r.world, &at)
                            };
                        }
                        let mut err = false;
                        for a in &args {
                            let mut r = self.resolve(*a, &p);
                            self.typecheck_as_set(&mut r, self.expr(*a).span);
                            err |= r.err;
                        }
                        self.record_spine(
                            e,
                            SpineChoice::Builtin {
                                op: BuiltinCall::Disj,
                            },
                        );
                        return R {
                            ty: self.formula(),
                            err,
                        };
                    }
                    "int" | "sum" => {
                        // Both `int[e]` and `sum[e]` are CAST2INT (§4.5).
                        let mut err = false;
                        for a in args {
                            let at = self.infer(a);
                            // A5 (int atoms): CAST2INT operand that can hold no Int
                            // atoms (§5.2). Position: the operand.
                            if at
                                .intersect(&self.r.world, &Type::unary(self.int_sig()))
                                .has_no_tuple(&self.r.world)
                            {
                                self.warnings.push(ResolveWarning::IntAtoms {
                                    span: self.expr(a).span,
                                });
                            }
                            let ap = at.remove_bool_and_int(self.int_sig());
                            let mut r = self.resolve(a, &ap);
                            self.typecheck_as_set(&mut r, self.expr(a).span);
                            err |= r.err;
                        }
                        self.record_spine(
                            e,
                            SpineChoice::Builtin {
                                op: BuiltinCall::IntCast,
                            },
                        );
                        return R {
                            ty: self.small_int(),
                            err,
                        };
                    }
                    "Int" => {
                        let mut err = false;
                        for a in args {
                            let ap = self.infer(a);
                            err |= self.resolve(a, &ap).err;
                        }
                        self.record_spine(
                            e,
                            SpineChoice::Builtin {
                                op: BuiltinCall::IntAtom,
                            },
                        );
                        return R {
                            ty: Type::unary(self.r.world.builtins.int),
                            err,
                        };
                    }
                    _ => {}
                }
            }
        }

        // A parameterized macro applied via box join or `.`-spine.
        if let Some((mid, arg_exprs)) = self.collect_macro_spine(e) {
            return self.expand_macro(e, mid, &arg_exprs, p);
        }

        // Build the readings of this application spine and pick.
        let readings = self.build_readings(e, span);
        self.pick_reading(e, readings, p, span)
    }

    /// Materializes the join-level `ExprChoice`: the candidate readings of an
    /// application spine (the reference's `Context.visit(JOIN)` + `process`).
    fn build_readings(&self, e: ExprId, span: Span) -> Vec<Reading> {
        match &self.expr(e).kind {
            ExprKind::Binary {
                op: BinOp::Join,
                lhs,
                rhs,
            } => {
                // `arg . right`: the right operand is the spine head, `lhs` the arg.
                let base = self.readings_of(*rhs, span);
                self.process_readings(base, *lhs, span)
            }
            ExprKind::BoxJoin { target, args } => {
                // `t[a,b] = b.(a.t)`: fold each arg into the target's readings.
                let mut base = self.readings_of(*target, span);
                for &a in args {
                    base = self.process_readings(base, a, span);
                }
                base
            }
            _ => Vec::new(),
        }
    }

    /// The head readings of a spine operand: a bare name → its candidate readings
    /// (`spine_head`); a nested join/box → its own readings (`build_readings`);
    /// anything else → a single sub-expr reading of its bottom-up type. Every
    /// reading records `head_expr = e` so the winning spine's base (mt-031) is
    /// recorded at the right node.
    fn readings_of(&self, e: ExprId, span: Span) -> Vec<Reading> {
        match &self.expr(e).kind {
            ExprKind::Name(_) => self.spine_head(e),
            ExprKind::Binary {
                op: BinOp::Join, ..
            }
            | ExprKind::BoxJoin { .. } => {
                // A nested spine: keep its readings but point `head_expr` at this
                // node so `flush_rec` records it as `Spine(Join)`.
                let mut rs = self.build_readings(e, span);
                for r in &mut rs {
                    r.head_expr = e;
                }
                rs
            }
            _ => vec![Reading {
                ty: self.infer(e),
                weight: 0,
                reason: "(expr)".to_owned(),
                fin: Fin::Sub(e),
                head_expr: e,
                head_choice: None,
            }],
        }
    }

    /// Applies argument `arg` to each reading (`Context.process`): a pending
    /// call gains the arg (→ `Call`/`BadCall`), a value/field reading becomes a
    /// relational join `arg . reading`.
    fn process_readings(&self, base: Vec<Reading>, arg: ExprId, span: Span) -> Vec<Reading> {
        let world = &self.r.world;
        let argt = self.infer(arg);
        let mut out = Vec::with_capacity(base.len());
        for reading in base {
            let head_expr = reading.head_expr;
            let head_choice = reading.head_choice.clone();
            let base_rec = Box::new(Self::rec_of(&reading));
            match reading.fin {
                Fin::BadCall {
                    func,
                    mut args,
                    this_arg,
                    span: cspan,
                } => {
                    // `Context.process`: if bc.args.size() < count, append arg;
                    // applicable(newargs) → Call, else BadCall. Otherwise (already
                    // full) → relational join `arg . badcall`.
                    let f = &self.r.world.funcs[func];
                    let count = f.params.len();
                    let params: Vec<Type> = f.params.iter().map(|pp| pp.ty.clone()).collect();
                    let this_ty = self
                        .rootsig
                        .map_or_else(Type::empty, |s| self.r.world.sigs[s].ty.clone());
                    let bc_size = usize::from(this_arg) + args.len();
                    if bc_size < count {
                        args.push(arg);
                        if self.args_applicable(&params, &args, this_arg.then(|| this_ty.clone())) {
                            let ret =
                                self.specialize_ret(func, this_arg.then_some(&this_ty), &args);
                            out.push(Reading {
                                ty: ret,
                                weight: reading.weight,
                                reason: reading.reason,
                                fin: Fin::Call {
                                    func,
                                    this_arg: this_arg.then_some(this_ty),
                                    args,
                                    span: cspan,
                                },
                                head_expr,
                                head_choice,
                            });
                        } else {
                            out.push(Reading {
                                ty: Type::empty(),
                                weight: reading.weight,
                                reason: reading.reason,
                                fin: Fin::BadCall {
                                    func,
                                    args,
                                    this_arg,
                                    span: cspan,
                                },
                                head_expr,
                                head_choice,
                            });
                        }
                    } else {
                        // Already full: a relational join of arg with the (bad) call.
                        let ty = argt.join(world, &reading.ty);
                        out.push(Reading {
                            ty,
                            weight: reading.weight,
                            reason: reading.reason,
                            fin: Fin::Join {
                                left: arg,
                                right_ty: reading.ty.clone(),
                                right_expr: None,
                                span,
                                base: base_rec,
                            },
                            head_expr,
                            head_choice,
                        });
                    }
                }
                // An unknown-name spine head stays a reject, not a relational join.
                Fin::Unknown { .. } => out.push(reading),
                other => {
                    // Relational join arg . reading (right is a resolved leaf).
                    // A `Sub(e)` right operand (a compound expr — closure,
                    // paren, nested join) is otherwise never resolved; carry it
                    // so `finalize` can collect its warnings (mt-023).
                    let right_expr = match other {
                        Fin::Sub(e) => Some(e),
                        _ => None,
                    };
                    let ty = argt.join(world, &reading.ty);
                    out.push(Reading {
                        ty,
                        weight: reading.weight,
                        reason: reading.reason,
                        fin: Fin::Join {
                            left: arg,
                            right_ty: reading.ty.clone(),
                            right_expr,
                            span,
                            base: base_rec,
                        },
                        head_expr,
                        head_choice,
                    });
                }
            }
        }
        out
    }

    /// The head readings of a spine: a bare name → its value candidates (leaf/
    /// this-join) + call/badcall readings; anything else → a single leaf reading
    /// of its bottom-up type.
    #[allow(clippy::too_many_lines)]
    fn spine_head(&self, e: ExprId) -> Vec<Reading> {
        match &self.expr(e).kind {
            ExprKind::Name(qn) => {
                let at_name = false;
                let segs = super::strip_this(qn.segments.iter().map(|s| s.text.clone()).collect());
                let mut out = Vec::new();
                // env var shadows.
                if segs.len() == 1 {
                    if let Some(t) = self.env_get(&segs[0]) {
                        out.push(Reading {
                            ty: t,
                            weight: 0,
                            reason: format!("var {}", segs[0]),
                            fin: Fin::Leaf,
                            head_expr: e,
                            head_choice: Some(CandOrigin::Var(segs[0].clone())),
                        });
                        return out;
                    }
                }
                if let Some(t) = self.builtin_value(&segs) {
                    out.push(Reading {
                        ty: t,
                        weight: 0,
                        reason: segs.join("/"),
                        fin: Fin::Leaf,
                        head_expr: e,
                        head_choice: builtin_value_choice(&segs).map(CandOrigin::Builtin),
                    });
                    return out;
                }
                // value candidates (leaf readings).
                for c in self.value_candidates(&segs, at_name) {
                    out.push(Reading {
                        ty: c.ty,
                        weight: c.weight,
                        reason: c.reason,
                        fin: Fin::Leaf,
                        head_expr: e,
                        head_choice: Some(c.origin),
                    });
                }
                // call/badcall readings.
                for fid in self.lookup_funcs(&segs) {
                    let f = &self.r.world.funcs[fid];
                    let reason = format!("{} {}", if f.is_pred { "pred" } else { "fun" }, f.name);
                    if f.params.is_empty() {
                        continue; // 0-ary already a value candidate above.
                    }
                    // implicit-this first-arg candidate (weight 1).
                    if let Some(root) = self.rootsig {
                        let this_ty = self.r.world.sigs[root].ty.clone();
                        if this_ty.has_arity(1)
                            && f.params[0].ty.intersects(&self.r.world, &this_ty)
                        {
                            out.push(Reading {
                                ty: Type::empty(),
                                weight: 1,
                                reason: format!(
                                    "{} this.{}",
                                    if f.is_pred { "pred" } else { "fun" },
                                    f.name
                                ),
                                fin: Fin::BadCall {
                                    func: fid,
                                    args: Vec::new(),
                                    this_arg: true,
                                    span: qn.span,
                                },
                                head_expr: e,
                                head_choice: None,
                            });
                        }
                    }
                    out.push(Reading {
                        ty: Type::empty(),
                        weight: 0,
                        reason,
                        fin: Fin::BadCall {
                            func: fid,
                            args: Vec::new(),
                            this_arg: false,
                            span: qn.span,
                        },
                        head_expr: e,
                        head_choice: None,
                    });
                }
                if out.is_empty() {
                    // A 0-param macro applied via box/join: expand to its body type.
                    if let Some(t) = self.infer_zero_macro(&segs) {
                        out.push(Reading {
                            ty: t,
                            weight: 0,
                            reason: segs.join("/"),
                            fin: Fin::Leaf,
                            head_expr: e,
                            head_choice: None,
                        });
                        return out;
                    }
                    // A callable-by-name (macro arg), meta/`$` name → lenient
                    // `univ` leaf; a genuinely unknown name → a reject reading.
                    let callable =
                        !self.lookup_funcs(&segs).is_empty() || self.lookup_macro(&segs).is_some();
                    let dollar = segs.iter().any(|s| s.contains('$')) || self.r.graph.seen_dollar;
                    if callable || dollar {
                        out.push(Reading {
                            ty: Type::unary(self.r.world.builtins.univ),
                            weight: 0,
                            reason: segs.join("/"),
                            fin: Fin::Leaf,
                            head_expr: e,
                            head_choice: None,
                        });
                    } else {
                        out.push(Reading {
                            ty: Type::unary(self.r.world.builtins.univ),
                            weight: 0,
                            reason: segs.join("/"),
                            fin: Fin::Unknown {
                                name: segs.join("/"),
                                span: qn.span,
                            },
                            head_expr: e,
                            head_choice: None,
                        });
                    }
                }
                out
            }
            // A parenthesized / compound right operand: a single leaf reading of
            // its bottom-up type (join-level ambiguity within it is resolved when
            // that subtree resolves).
            _ => vec![Reading {
                ty: self.infer(e),
                weight: 0,
                reason: "(expr)".to_owned(),
                fin: Fin::Sub(e),
                head_expr: e,
                head_choice: None,
            }],
        }
    }

    /// The reference's `DeduceType` per-call return-type specialization: re-infer
    /// the fun's return-decl expr with each param bound to the actual arg type
    /// (extracted to the param's arity), giving a tighter type at the call site
    /// (`dom[grades]` → `Course`, not the declared `univ`). Falls back to the
    /// declared type on any int/bool/arity change (as the reference does). Only
    /// attempted when the declared return contains `univ` (the imprecise case),
    /// to bound cost.
    fn specialize_ret(&self, func: FuncId, this_ty: Option<&Type>, args: &[ExprId]) -> Type {
        let f = &self.r.world.funcs[func];
        let declared = f.return_ty.clone();
        if f.is_pred || self.unroll == 0 || !self.contains_univ(&declared) {
            return declared;
        }
        let Some(rd) = f.return_decl else {
            return declared;
        };
        let mut argtys: Vec<Type> = Vec::new();
        if let Some(t) = this_ty {
            argtys.push(t.clone());
        }
        for &a in args {
            argtys.push(self.infer(a));
        }
        if argtys.len() != f.params.len() {
            return declared;
        }
        let module = f.module;
        let params: Vec<(String, usize)> = f
            .params
            .iter()
            .map(|p| (p.name.clone(), p.ty.arity().unwrap_or(1).max(1)))
            .collect();
        let mut sub = Cx::new(self.r, module);
        sub.unroll = self.unroll - 1;
        for ((name, ar), at) in params.iter().zip(&argtys) {
            sub.env.push((name.clone(), at.extract(&self.r.world, *ar)));
        }
        let t = sub.infer(rd).remove_bool_and_int(self.int_sig());
        if t.is_error()
            || t.is_bool
            || t.is_small_int
            || t.is_int(&self.r.world)
            || t.arity() != declared.arity()
        {
            declared
        } else {
            t
        }
    }

    /// Whether every argument is applicable to its parameter (§4.4 `applicable`):
    /// common arity, and — only when both are non-empty — intersecting. An
    /// implicit `this` first arg is prepended.
    fn args_applicable(&self, params: &[Type], args: &[ExprId], this_ty: Option<Type>) -> bool {
        let world = &self.r.world;
        let mut argtys: Vec<Type> = Vec::new();
        if let Some(t) = this_ty {
            argtys.push(t);
        }
        for &a in args {
            argtys.push(self.infer(a));
        }
        // `applicable`: false if fewer args than params; else check each param.
        if params.len() > argtys.len() {
            return false;
        }
        params.iter().zip(&argtys).all(|(p, a)| {
            if a.is_error() || p.is_error() {
                return true;
            }
            if !a.has_common_arity(p) {
                return false;
            }
            !(a.has_tuple(world) && p.has_tuple(world) && !a.intersects(world, p))
        })
    }

    /// Picks a reading of the join-level choice against relevant type `p`
    /// (`resolveHelper`), then finalizes it (resolve operands / args, emit
    /// errors).
    fn pick_reading(&mut self, e: ExprId, mut readings: Vec<Reading>, p: &Type, span: Span) -> R {
        if readings.is_empty() {
            return R::bad();
        }
        if readings.len() == 1 {
            let only = readings.swap_remove(0);
            return self.finalize_recorded(e, only, p);
        }
        let types: Vec<Type> = readings.iter().map(|r| r.ty.clone()).collect();
        let weights: Vec<i32> = readings.iter().map(|r| r.weight).collect();
        match self.resolve_helper(&types, &weights, p) {
            Pick::One(i) => {
                let reading = readings.swap_remove(i);
                self.finalize_recorded(e, reading, p)
            }
            Pick::NoneArity(k) => {
                self.record_spine(e, SpineChoice::Empty(k));
                R::ok(self.none_of_arity(k))
            }
            Pick::Ambiguous(idxs) => {
                if self.lenient() {
                    let reading = readings.swap_remove(idxs[0]);
                    return self.finalize_lenient(reading, p);
                }
                // If the surviving readings are all failed calls (BadCall), it is a
                // "possible incorrect function/predicate call", not an ambiguity.
                let all_bad = idxs
                    .iter()
                    .all(|&i| matches!(readings[i].fin, Fin::BadCall { .. }));
                if all_bad {
                    self.err(ResolveError::BadCall {
                        name: readings[idxs[0]].reason.clone(),
                        span,
                    });
                } else {
                    self.err(ResolveError::AmbiguousName {
                        name: readings[idxs[0]].reason.clone(),
                        span,
                        candidates: idxs.iter().map(|&i| readings[i].reason.clone()).collect(),
                    });
                }
                R::bad()
            }
            Pick::NoIntersect => {
                if self.lenient() {
                    let reading = readings.swap_remove(0);
                    return self.finalize_lenient(reading, p);
                }
                // No reading matches the relevant type. If any reading is a bad call,
                // report BadCall; else the join is illegal (both operands unary).
                let any_bad = readings
                    .iter()
                    .any(|r| matches!(r.fin, Fin::BadCall { .. }));
                if any_bad {
                    self.err(ResolveError::BadCall {
                        name: readings[0].reason.clone(),
                        span,
                    });
                    R::bad()
                } else {
                    // finalize the first reading to surface a precise join error.
                    let reading = readings.swap_remove(0);
                    self.finalize_recorded(e, reading, p)
                }
            }
        }
    }

    /// Records the winning spine reading's choice (mt-031) — the node as a
    /// join / call, and (for a join) its base name — then finalizes it.
    fn finalize_recorded(&mut self, e: ExprId, reading: Reading, p: &Type) -> R {
        match &reading.fin {
            Fin::Join { base, left, .. } => {
                self.record_spine(e, SpineChoice::Join);
                let base = base.clone();
                let receiver = *left;
                self.flush_rec(&base, Some(receiver));
            }
            Fin::Call {
                func,
                this_arg,
                args,
                ..
            } => {
                self.record_spine(
                    e,
                    SpineChoice::Call(CallChoice {
                        func: *func,
                        implicit_this: this_arg.is_some(),
                        args: args.clone(),
                    }),
                );
            }
            Fin::Leaf | Fin::Sub(_) | Fin::BadCall { .. } | Fin::Unknown { .. } => {}
        }
        self.finalize_reading(reading, p)
    }

    /// Lenient finalize (a `$`-meta model): resolve the chosen reading but never
    /// let it reject — a `BadCall` becomes a lenient `univ` value.
    fn finalize_lenient(&mut self, reading: Reading, p: &Type) -> R {
        if matches!(reading.fin, Fin::BadCall { .. } | Fin::Unknown { .. }) {
            return R::ok(Type::unary(self.r.world.builtins.univ));
        }
        let mut r = self.finalize_reading(reading, p);
        r.err = false;
        r
    }

    /// Finalizes a chosen reading: resolves its operands against slices derived
    /// from `p`, and emits any make-error (illegal join / bad call).
    fn finalize_reading(&mut self, reading: Reading, p: &Type) -> R {
        match reading.fin {
            Fin::Leaf => R::ok(reading.ty),
            Fin::Sub(e) => self.resolve(e, p),
            Fin::Unknown { name, span } => {
                if self.lenient() {
                    return R::ok(reading.ty);
                }
                self.err(ResolveError::UnknownName { name, span });
                R::bad()
            }
            Fin::Join {
                left,
                right_ty,
                right_expr,
                span,
                base: _,
            } => {
                // Resolve the left operand (which may itself be a join/choice).
                // A compound right operand (`s.*next`, `x.(y.z)`) keeps its
                // bottom-up type for the *verdict* rather than being resolved
                // standalone — standalone resolution loses the join's
                // disambiguation (`*next` becomes ambiguous with the auto-opened
                // `integer/next`); a documented over-acceptance for an unknown
                // name inside a compound right operand (LIMITATIONS), never a
                // false reject.
                let lt = self.infer(left);
                let (ap, bp) = self.join_slices(&lt, &right_ty, p);
                let mut l = self.resolve(left, &ap);
                self.typecheck_as_set(&mut l, self.expr(left).span);
                // Warning-only pass over the compound right operand (mt-023): the
                // reference resolves it (emitting any relevance/redundancy warning
                // inside, e.g. a `^`-closure), so mettle collects those warnings
                // too — but discards any *errors* it raises, keeping the verdict
                // byte-identical (the LIMITATIONS over-acceptance is preserved).
                if let Some(re) = right_expr {
                    let nerr = self.errors.len();
                    let _ = self.resolve(re, &bp);
                    self.errors.truncate(nerr);
                }
                let joined = lt.join(&self.r.world, &right_ty);
                // `$`-meta models resolve leniently (meta atoms mettle approximates
                // as `univ`); a lenient `univ`/placeholder operand is never a
                // genuine illegal join.
                if !l.err
                    && joined.is_error()
                    && !self.r.graph.seen_dollar
                    && !self.contains_univ(&lt)
                    && !self.contains_univ(&right_ty)
                {
                    self.err(ResolveError::IllegalJoin { span });
                    return R::bad();
                }
                // A9: a legal-arity join whose type is statically empty (§5.2
                // `this.type.hasNoTuple()`). EMPTY (illegal join) took the reject
                // path above; a `univ` operand is a lenient placeholder, not a
                // genuine empty join.
                if !l.err
                    && !joined.is_error()
                    && joined.has_no_tuple(&self.r.world)
                    && !self.contains_univ(&lt)
                    && !self.contains_univ(&right_ty)
                {
                    self.warnings.push(ResolveWarning::JoinEmpty { span });
                }
                R {
                    ty: joined,
                    err: l.err,
                }
            }
            Fin::Call {
                func,
                this_arg,
                args,
                span,
            } => {
                if self.no_calls {
                    self.err(ResolveError::FieldBoundHasCall {
                        name: self.field_name.clone(),
                        span,
                    });
                }
                let f = &self.r.world.funcs[func];
                let params: Vec<Type> = f.params.iter().map(|pp| pp.ty.clone()).collect();
                let ret = self.specialize_ret(func, this_arg.as_ref(), &args);
                // Resolve each explicit arg against its parameter type, then
                // typecheck_as_set (ExprCall.resolve).
                let offset = usize::from(this_arg.is_some());
                let mut err = false;
                for (k, &a) in args.iter().enumerate() {
                    let pk = params.get(offset + k).cloned().unwrap_or_else(Type::empty);
                    let mut r = self.resolve(a, &pk);
                    self.typecheck_as_set(&mut r, self.expr(a).span);
                    err |= r.err;
                }
                R { ty: ret, err }
            }
            Fin::BadCall { func, span, .. } => {
                let name = self.r.world.funcs[func].name.clone();
                self.err(ResolveError::BadCall { name, span });
                R::bad()
            }
        }
    }

    /// The reference JOIN resolve slice for the **left** operand `a` (and right
    /// `b`), given the join's relevant type `p` and the operands' bottom-up
    /// types (resolution-doc §4.3, the 3-block algorithm).
    #[allow(clippy::many_single_char_names)]
    fn join_slices(&self, left: &Type, right: &Type, p: &Type) -> (Type, Type) {
        let world = &self.r.world;
        // Block 1: precise slice with p.intersect(aa.join(bb)).
        let mut a = Type::empty();
        let mut b = Type::empty();
        for aa in &left.entries {
            for bb in &right.entries {
                let jarity = aa.arity() + bb.arity();
                if jarity < 2 || !p.has_arity(jarity - 2) {
                    continue;
                }
                let j = col_meet(world, aa.0[aa.arity() - 1], bb.0[0]);
                if j == world.builtins.none {
                    continue;
                }
                let aajoin =
                    Type::product_of(aa.0.clone()).join(world, &Type::product_of(bb.0.clone()));
                let inter = p.intersect(world, &aajoin);
                for cc in &inter.entries {
                    if cc.is_empty(world) {
                        continue;
                    }
                    // reconstruct v = cc with j inserted at (aa.arity()-1).
                    let mut v: Vec<SigId> = cc.0.clone();
                    v.insert(aa.arity() - 1, j);
                    let al = v[..aa.arity()].to_vec();
                    let bl = v[aa.arity() - 1..].to_vec();
                    a = a.union(world, &Type::product_of(al));
                    b = b.union(world, &Type::product_of(bl));
                }
            }
        }
        if !a.is_error() && !b.is_error() {
            return (a, b);
        }
        // Block 2: fallback on intersects (drop the p.intersect non-empty filter).
        let mut a2 = Type::empty();
        let mut b2 = Type::empty();
        for aa in &left.entries {
            for bb in &right.entries {
                let jarity = aa.arity() + bb.arity();
                if jarity < 2 || !p.has_arity(jarity - 2) {
                    continue;
                }
                if col_intersects(world, aa.0[aa.arity() - 1], bb.0[0]) {
                    a2 = a2.union(world, &Type::product_of(aa.0.clone()));
                    b2 = b2.union(world, &Type::product_of(bb.0.clone()));
                }
            }
        }
        if !a2.is_error() && !b2.is_error() {
            return (a2, b2);
        }
        // Block 3: fallback merging all common-arity pairs.
        let mut a3 = Type::empty();
        let mut b3 = Type::empty();
        for aa in &left.entries {
            for bb in &right.entries {
                let jarity = aa.arity() + bb.arity();
                if jarity < 2 || !p.has_arity(jarity - 2) {
                    continue;
                }
                a3 = a3.union(world, &Type::product_of(aa.0.clone()));
                b3 = b3.union(world, &Type::product_of(bb.0.clone()));
            }
        }
        (a3, b3)
    }

    /// Collects a macro-application spine (§3.7).
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
                // Only a *parameterized* macro consumes the join LHS as an
                // argument (`x.m[..]` = `m[x,..]`). A 0-param macro on the right
                // of a join is a plain relational join `x . (expand m)` — handled
                // by `build_readings` (`infer_zero_macro`), not a macro spine.
                if self.r.world.macros[mid].params.is_empty() {
                    None
                } else {
                    Some((mid, vec![*lhs]))
                }
            }
            _ => None,
        }
    }

    // ---- binders ----

    fn quant(&mut self, quant: Quant, decls: &[DeclId], body: ExprId, span: Span) -> R {
        let pushed = self.bind_decls(decls);
        let err = if matches!(quant, Quant::Sum) {
            let ip = self.small_int();
            self.resolve_checked(body, &ip).err
        } else {
            let fp = self.formula();
            self.resolve_checked(body, &fp).err
        };
        self.pop_and_warn_unused(decls, body, pushed);
        let _ = span;
        let ty = if matches!(quant, Quant::Sum) {
            self.small_int()
        } else {
            self.formula()
        };
        R { ty, err }
    }

    fn comprehension(&mut self, decls: &[DeclId], body: ExprId) -> R {
        // Bind the decls once, capturing each variable's element type (the
        // comprehension result type is their product, in order). Re-resolving
        // the bounds here would re-pick under the now-shadowed env — wrong when
        // a decl redeclares an earlier name (`{p:A, …, p:f[p]}`).
        let (pushed, types) = self.bind_decls_typed(decls);
        let fp = self.formula();
        let err = self.resolve_checked(body, &fp).err;
        let mut ty: Option<Type> = None;
        for bt in &types {
            ty = Some(match ty {
                None => bt.clone(),
                Some(prev) => prev.product(&self.r.world, bt),
            });
        }
        // Comprehensions are exempt from the unused-variable warning
        // (`ExprQt.resolve`: `op != Op.COMPREHENSION`, resolution-doc §5.2 B).
        for _ in 0..pushed {
            self.env.pop();
        }
        R {
            ty: ty.unwrap_or_else(Type::empty),
            err,
        }
    }

    fn let_expr(&mut self, bindings: &[LetBinding], body: ExprId, p: &Type) -> R {
        let mut pushed = 0;
        for b in bindings {
            let bp = self.infer(b.value);
            let t = self.resolve(b.value, &bp).ty;
            self.env.push((b.name.text.clone(), t));
            pushed += 1;
        }
        let out = self.resolve(body, p);
        for _ in 0..pushed {
            self.env.pop();
        }
        // Unused `let` variable (`ExprLet.resolve`: `!newSub.hasVar(var)`,
        // resolution-doc §5.2 B). Desugared `let x=a, y=b | body` is nested lets,
        // so `x` is used iff a later binding value or the body references it
        // (syntactic `hasVar`). Position: the name.
        for (i, b) in bindings.iter().enumerate() {
            let used_later = bindings[i + 1..]
                .iter()
                .any(|nb| self.references_name(nb.value, &b.name.text));
            if !used_later && !self.references_name(body, &b.name.text) {
                self.warnings.push(ResolveWarning::UnusedVariable {
                    name: b.name.text.clone(),
                    span: b.name.span,
                });
            }
        }
        out
    }

    fn bind_decls(&mut self, decls: &[DeclId]) -> usize {
        self.bind_decls_typed(decls).0
    }

    /// Binds a decl list into the env, returning how many env frames to pop and
    /// each pushed variable's element type (in push order) — resolved **once**
    /// with the correct incremental env.
    fn bind_decls_typed(&mut self, decls: &[DeclId]) -> (usize, Vec<Type>) {
        let mut pushed = 0;
        let mut types = Vec::new();
        for &d in decls {
            let decl = self.ast().decls[d].clone();
            let bt = self.decl_bound_type(&decl);
            for name in &decl.names {
                self.env.push((name.text.clone(), bt.clone()));
                types.push(bt.clone());
                pushed += 1;
            }
        }
        (pushed, types)
    }

    fn decl_bound_type(&mut self, decl: &Decl) -> Type {
        let p = self.infer(decl.bound).remove_bool_and_int(self.int_sig());
        let mut r = self.resolve(decl.bound, &p);
        self.typecheck_as_set(&mut r, self.expr(decl.bound).span);
        r.ty.as_set(self.int_sig())
    }

    /// Pops the `pushed` binder frames and emits an unused-variable warning for
    /// each quantifier variable the reference would (`ExprQt.resolve`,
    /// resolution-doc §5.2 B): a variable `x` in group `i` is warned iff **no
    /// later decl group's bound references `x`** and **the body does not
    /// reference `x`**. "References" is the reference's syntactic `hasVar`
    /// ([`Self::references_name`]), not a resolve-time side effect — a variable
    /// used only as a join spine head (`proc.p`) still counts as used.
    fn pop_and_warn_unused(&mut self, decls: &[DeclId], body: ExprId, pushed: usize) {
        for _ in 0..pushed {
            self.env.pop();
        }
        for (i, &d) in decls.iter().enumerate() {
            let decl = self.ast().decls[d].clone();
            let later_bounds: Vec<ExprId> = decls[i + 1..]
                .iter()
                .map(|&dj| self.ast().decls[dj].bound)
                .collect();
            for n in &decl.names {
                let used_later = later_bounds
                    .iter()
                    .any(|&b| self.references_name(b, &n.text));
                if !used_later && !self.references_name(body, &n.text) {
                    self.warnings.push(ResolveWarning::UnusedVariable {
                        name: n.text.clone(),
                        span: n.span,
                    });
                }
            }
        }
    }

    /// The reference's `ExprUnary.resolveClosure(parent, child)` (A2): the child
    /// (binary) tuples `c1->c2` that lie on some closure path `p1..c1..c2..p2`
    /// for a parent tuple `p1->p2`. Returns `EMPTY` when the closure contributes
    /// nothing to `parent` — the "does not contribute" trigger. A faithful port
    /// of the directed-graph reachability over prim-sig columns.
    fn resolve_closure(&self, parent: &Type, child: &Type) -> Type {
        use std::collections::{BTreeMap, BTreeSet};
        let w = &self.r.world;
        let mut nodes: BTreeSet<usize> = BTreeSet::new();
        let mut adj: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        let add_edge = |a: SigId, b: SigId, adj: &mut BTreeMap<usize, BTreeSet<usize>>| {
            adj.entry(a.index()).or_default().insert(b.index());
        };
        // Child binary edges.
        for c in &child.entries {
            if c.arity() == 2 {
                nodes.insert(c.0[0].index());
                nodes.insert(c.0[1].index());
                add_edge(c.0[0], c.0[1], &mut adj);
            }
        }
        // Connect intersecting nodes both ways.
        let node_vec: Vec<usize> = nodes.iter().copied().collect();
        for &a in &node_vec {
            for &b in &node_vec {
                if a != b && col_intersects(w, SigId::from_index(a), SigId::from_index(b)) {
                    add_edge(SigId::from_index(a), SigId::from_index(b), &mut adj);
                }
            }
        }
        // Parent tuples: introduce their columns, linking to intersecting nodes.
        for p in &parent.entries {
            if p.arity() != 2 {
                continue;
            }
            for &col in &[p.0[0], p.0[1]] {
                if !nodes.contains(&col.index()) {
                    let cur: Vec<usize> = nodes.iter().copied().collect();
                    for &x in &cur {
                        if col_intersects(w, col, SigId::from_index(x)) {
                            add_edge(col, SigId::from_index(x), &mut adj);
                            add_edge(SigId::from_index(x), col, &mut adj);
                        }
                    }
                    nodes.insert(col.index());
                }
            }
        }
        // A child edge survives iff some parent tuple reaches through it.
        let has_path = |from: usize, to: usize, adj: &BTreeMap<usize, BTreeSet<usize>>| -> bool {
            if from == to {
                return true;
            }
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            let mut stack = vec![from];
            seen.insert(from);
            while let Some(n) = stack.pop() {
                if let Some(next) = adj.get(&n) {
                    for &m in next {
                        if m == to {
                            return true;
                        }
                        if seen.insert(m) {
                            stack.push(m);
                        }
                    }
                }
            }
            false
        };
        let mut answer = Type::empty();
        for c in &child.entries {
            if c.arity() != 2 {
                continue;
            }
            let (c1, c2) = (c.0[0].index(), c.0[1].index());
            for p in &parent.entries {
                if p.arity() != 2 {
                    continue;
                }
                let (p1, p2) = (p.0[0].index(), p.0[1].index());
                if has_path(p1, c1, &adj) && has_path(c2, p2, &adj) {
                    answer = answer.merge(w, &Type::product_of(c.0.clone()));
                    break;
                }
            }
        }
        answer
    }

    /// Whether expression `e` syntactically references a bare variable named
    /// `name`, honoring shadowing (a nested binder that rebinds `name` hides it
    /// in the shadowed scope) — the reference's `Expr.hasVar`.
    fn references_name(&self, e: ExprId, name: &str) -> bool {
        match &self.expr(e).kind {
            ExprKind::Name(qn) | ExprKind::AtName(qn) => {
                qn.segments.len() == 1 && qn.segments[0].text == name
            }
            ExprKind::Num(_) | ExprKind::Str(_) | ExprKind::Const(_) | ExprKind::This => false,
            ExprKind::Unary { expr, .. } => self.references_name(*expr, name),
            ExprKind::Binary { lhs, rhs, .. }
            | ExprKind::Arrow { lhs, rhs, .. }
            | ExprKind::Compare { lhs, rhs, .. } => {
                self.references_name(*lhs, name) || self.references_name(*rhs, name)
            }
            ExprKind::BoxJoin { target, args } => {
                self.references_name(*target, name)
                    || args.iter().any(|&a| self.references_name(a, name))
            }
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.references_name(*cond, name)
                    || self.references_name(*then_branch, name)
                    || self.references_name(*else_branch, name)
            }
            ExprKind::Quant { decls, body, .. } | ExprKind::Comprehension { decls, body } => {
                self.decls_or_body_reference(decls, *body, name)
            }
            ExprKind::Let { bindings, body } => {
                // Binding values are sequential (later see earlier); the body is
                // shadowed once a binding rebinds `name`.
                let mut shadowed = false;
                for b in bindings {
                    if !shadowed && self.references_name(b.value, name) {
                        return true;
                    }
                    if b.name.text == name {
                        shadowed = true;
                    }
                }
                !shadowed && self.references_name(*body, name)
            }
            ExprKind::Block(exprs) => exprs.iter().any(|&f| self.references_name(f, name)),
        }
    }

    /// `references_name` for a `Quant`/`Comprehension`: search each decl bound
    /// (evaluated in the outer scope, up to the point `name` is rebound), then
    /// the body iff no decl rebinds `name`.
    fn decls_or_body_reference(&self, decls: &[DeclId], body: ExprId, name: &str) -> bool {
        let mut shadowed = false;
        for &d in decls {
            let decl = &self.ast().decls[d];
            if !shadowed && self.references_name(decl.bound, name) {
                return true;
            }
            if decl.names.iter().any(|n| n.text == name) {
                shadowed = true;
            }
        }
        !shadowed && self.references_name(body, name)
    }

    // ---- helpers ----

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

    /// Whether byte offsets `end` (exclusive end of the first formula) and
    /// `start` (start of the second) sit on the same source line — the byte-span
    /// equivalent of the reference's `a.span().y2 == b.span().y` (no newline
    /// between). Reads the file's source from the module graph.
    fn same_source_line(&self, file: als_syntax::FileId, end: u32, start: u32) -> bool {
        if start < end {
            return false;
        }
        let src = &self.r.graph.files.file(file).source;
        let (lo, hi) = (end as usize, start as usize);
        if hi > src.len() {
            return false;
        }
        !src.as_bytes()[lo..hi].contains(&b'\n')
    }

    /// Structural expression equality ignoring spans (the reference's
    /// `Expr.isSame`, resolution-doc §5.2 A3/A4 "same value"). Conservative: a
    /// `false` never causes a *missing* reject (this only gates a warning), so
    /// unhandled shapes simply do not fire the redundancy warning.
    fn same_expr(&self, a: ExprId, b: ExprId) -> bool {
        if a == b {
            return true;
        }
        let (ka, kb) = (&self.expr(a).kind, &self.expr(b).kind);
        match (ka, kb) {
            (ExprKind::Num(x), ExprKind::Num(y)) => x == y,
            (ExprKind::Str(x), ExprKind::Str(y)) => x == y,
            (ExprKind::Const(x), ExprKind::Const(y)) => x == y,
            (ExprKind::This, ExprKind::This) => true,
            (ExprKind::Name(x), ExprKind::Name(y)) | (ExprKind::AtName(x), ExprKind::AtName(y)) => {
                seg_eq(x, y)
            }
            (ExprKind::Unary { op: oa, expr: ea }, ExprKind::Unary { op: ob, expr: eb }) => {
                oa == ob && self.same_expr(*ea, *eb)
            }
            (
                ExprKind::Binary {
                    op: oa,
                    lhs: la,
                    rhs: ra,
                },
                ExprKind::Binary {
                    op: ob,
                    lhs: lb,
                    rhs: rb,
                },
            ) => oa == ob && self.same_expr(*la, *lb) && self.same_expr(*ra, *rb),
            (
                ExprKind::Compare {
                    op: oa,
                    negated: na,
                    lhs: la,
                    rhs: ra,
                },
                ExprKind::Compare {
                    op: ob,
                    negated: nb,
                    lhs: lb,
                    rhs: rb,
                },
            ) => oa == ob && na == nb && self.same_expr(*la, *lb) && self.same_expr(*ra, *rb),
            (
                ExprKind::Arrow {
                    lhs: la, rhs: ra, ..
                },
                ExprKind::Arrow {
                    lhs: lb, rhs: rb, ..
                },
            ) => self.same_expr(*la, *lb) && self.same_expr(*ra, *rb),
            (
                ExprKind::BoxJoin {
                    target: ta,
                    args: aa,
                },
                ExprKind::BoxJoin {
                    target: tb,
                    args: ab,
                },
            ) => {
                aa.len() == ab.len()
                    && self.same_expr(*ta, *tb)
                    && aa.iter().zip(ab).all(|(&x, &y)| self.same_expr(x, y))
            }
            _ => false,
        }
    }
}

/// The [`BuiltinValue`] a `fun/…` name denotes (resolution-doc §4.5), for choice
/// recording (mt-031).
fn builtin_value_choice(segs: &[String]) -> Option<BuiltinValue> {
    match segs.join("/").as_str() {
        "fun/min" => Some(BuiltinValue::IntMin),
        "fun/max" => Some(BuiltinValue::IntMax),
        "fun/next" => Some(BuiltinValue::IntNext),
        "fun/prev" => Some(BuiltinValue::IntPrev),
        _ => None,
    }
}

/// Segment-text equality of two qualified names (span-free).
fn seg_eq(a: &QualName, b: &QualName) -> bool {
    a.segments.len() == b.segments.len()
        && a.segments
            .iter()
            .zip(&b.segments)
            .all(|(x, y)| x.text == y.text)
}

/// The outcome of `resolveHelper` over a candidate type list.
enum Pick {
    /// Exactly one survivor: its index.
    One(usize),
    /// All survivors collapse to the same-arity empty set → `none` of arity `k`.
    NoneArity(usize),
    /// Two or more genuine survivors: ambiguous (their indices).
    Ambiguous(Vec<usize>),
    /// No survivor matches the relevant type at all.
    NoIntersect,
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

/// `ProductType.columnRestrict`: restrict column `idx` of `p` by sig `b`, or a
/// `NONE`-filled product of the same arity if the meet is empty.
fn restrict_col(
    w: &crate::world::ResolvedWorld,
    p: &crate::ty::Product,
    b: SigId,
    idx: usize,
) -> crate::ty::Product {
    use crate::ty::Product;
    if p.is_empty(w) || idx >= p.arity() {
        return p.clone();
    }
    let c = col_meet(w, p.0[idx], b);
    if c == w.builtins.none {
        return Product(vec![w.builtins.none; p.arity()]);
    }
    let mut cols = p.0.clone();
    cols[idx] = c;
    Product(cols)
}

/// The meet of two prim-sig columns (`PrimSig.intersect`).
fn col_meet(w: &crate::world::ResolvedWorld, a: SigId, b: SigId) -> SigId {
    if w.is_same_or_descendent(a, b) {
        a
    } else if w.is_same_or_descendent(b, a) {
        b
    } else {
        w.builtins.none
    }
}

/// Whether two prim-sig columns have a non-empty meet (`PrimSig.intersects`).
fn col_intersects(w: &crate::world::ResolvedWorld, a: SigId, b: SigId) -> bool {
    let none = w.builtins.none;
    if w.is_same_or_descendent(a, b) {
        a != none
    } else if w.is_same_or_descendent(b, a) {
        b != none
    } else {
        false
    }
}
