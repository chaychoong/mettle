//! Resolution **choices** — the seam the translator (mt-031, `als_core::lower`)
//! consumes so it never re-derives name resolution or overload choice
//! (resolution-doc §4.4; the §4.4 candidate chain took two beads to get right,
//! so duplicating it in the lowerer would be drift). Additive mt-031 widening.
//!
//! The type checker ([`crate::resolve`]) already materializes, for every
//! resolved name and application spine, exactly one reading (which sig / field /
//! call / join / macro it settled on). It records that decision here, keyed by
//! **`(ModuleId, ExprId)`** — never `ExprId` alone: one file's AST is shared
//! across module instances (identity = file + args, mt-017), and the same
//! `ExprId` can resolve differently per instance.
//!
//! Only three surface node families carry a choice:
//! - a bare [`als_syntax::ast::ExprKind::Name`]/`AtName` → a [`NameChoice`];
//! - an application spine ([`als_syntax::ast::ExprKind::Binary`] with
//!   [`als_syntax::ast::BinOp::Join`], or a [`als_syntax::ast::ExprKind::BoxJoin`])
//!   → a [`SpineChoice`];
//! - a [`als_syntax::ast::ExprKind::Quant`]/`Comprehension` **ground-expanded**
//!   over the `$` metamodel → a [`MetaExpansion`] (mt-107 P2). This is the one
//!   choice that does not *select* a reading: it replaces the node with a fold
//!   of N re-resolved copies of its body.
//!
//! Every other `ExprKind` lowers structurally (the lowerer recurses), so it
//! needs no recorded choice. `Num`/`Str`/`Const`/`This` are handled by the
//! lowerer directly (a literal, a constant, the enclosing binder).

use std::collections::BTreeMap;

use als_syntax::ast::ExprId;

use crate::graph::ModuleId;
use crate::world::{FieldId, FuncId, MacroId, SigId};

/// The recorded resolution of one `Name`/`AtName` or application-spine node.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExprChoice {
    /// A bare name resolved to a leaf value.
    Name(NameChoice),
    /// An application spine resolved to a join / call / builtin / macro.
    Spine(SpineChoice),
    /// A quantifier/comprehension the phase-8 `$` metamodel **ground expansion**
    /// replaced with a fold over the meta atoms (mt-107 P2).
    Meta(MetaExpansion),
}

/// What a bare `Name`/`AtName` resolved to (resolution-doc §4.4 `populate`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum NameChoice {
    /// A lexically-bound variable (quantifier / comprehension / `let` / func
    /// param / `this`), identified by the name written. The lowerer keeps a
    /// binder stack mirroring the checker's env, so innermost-wins resolves the
    /// exact binding (honoring shadowing).
    Var(String),
    /// A signature (prim, subset, or builtin `Int`/`seq/Int`/`String`).
    Sig(SigId),
    /// A field relation. `implicit_this` is `true` for a bare field reference in
    /// a sig context (`f` ⇒ `this . f`, resolution-doc §3.3); `false` for `@f`,
    /// a cross-branch reference, or a field outside any sig.
    Field {
        /// The chosen field.
        field: FieldId,
        /// Whether an implicit `this .` receiver is inserted.
        implicit_this: bool,
    },
    /// A 0-ary func/pred referenced as a value — its body is inlined with no
    /// arguments (a pred body is a formula, a fun body a relation/int).
    Call0(FuncId),
    /// A relational/constant builtin value spelled as a name
    /// (`fun/min`/`fun/max` → `Int`; `fun/next`/`fun/prev` → `Int -> Int`).
    Builtin(BuiltinValue),
    /// A 0-param macro used as a value — replay via [`MacroChoice`].
    Macro(MacroChoice),
    /// The candidate set collapsed to `none` of a fixed arity (resolution-doc
    /// §4.4 `resolveHelper` `NoneArity`) — the value is the empty relation.
    EmptyArity(usize),
}

/// A builtin relational value spelled with a `fun/…` name (resolution-doc §4.5).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BuiltinValue {
    /// `fun/min` — the least `Int` atom in scope.
    IntMin,
    /// `fun/max` — the greatest `Int` atom in scope.
    IntMax,
    /// `fun/next` — the integer successor relation.
    IntNext,
    /// `fun/prev` — the integer predecessor relation.
    IntPrev,
}

/// What an application spine (`a.b`, `f[x]`, `a.f[x]`) resolved to.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SpineChoice {
    /// A relational join. The lowerer recurses into the node's operands
    /// structurally (`Binary{Join}` → `lower(lhs) . lower(rhs)`; `BoxJoin` →
    /// `t[a,b]` = `b . (a . t)`).
    Join,
    /// A func/pred call — inline the callee's body with each parameter bound to
    /// the corresponding (already-lowered) argument (resolution-doc §3.5).
    Call(CallChoice),
    /// A builtin box-join form (`disj[..]`, `pred/totalOrder[..]`, `int[..]`,
    /// `sum[..]`, `Int[..]`).
    Builtin {
        /// Which builtin form.
        op: BuiltinCall,
    },
    /// A macro application — replay via [`MacroChoice`].
    Macro(MacroChoice),
    /// The spine's candidate readings collapsed to `none` of a fixed arity
    /// (resolution-doc §4.4 `resolveHelper` `NoneArity`): the value is the empty
    /// relation of that arity.
    Empty(usize),
}

/// A resolved func/pred call (resolution-doc §4.4 `ExprCall`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CallChoice {
    /// The chosen overload.
    pub func: FuncId,
    /// Whether an implicit `this` is the receiver (first argument).
    pub implicit_this: bool,
    /// Explicit argument expressions, in parameter order (after any implicit
    /// `this`), each an [`ExprId`] in the calling module.
    pub args: Vec<ExprId>,
}

/// A builtin box-join operator (resolution-doc §4.5).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BuiltinCall {
    /// `disj[a, b, …]` — pairwise disjointness.
    Disj,
    /// `pred/totalOrder[elem, first, next]`.
    TotalOrder,
    /// `int[e]` / `sum[e]` — cast a set of `Int` atoms to an integer value.
    IntCast,
    /// `Int[ie]` — the `Int` atom(s) carrying an integer value.
    IntAtom,
}

/// A macro replay record (resolution-doc §3.7). Macro expansion is textual and
/// per-call-site: the same macro body `ExprId` can resolve differently at two
/// call sites (different argument types), so the body's choices are recorded in
/// a **nested** [`ChoiceTable`] captured *at this site*, not merged into the
/// outer one.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MacroChoice {
    /// The macro whose body replaces this node.
    pub macro_id: MacroId,
    /// The module the macro body lives in (its choices are keyed under it).
    pub body_module: ModuleId,
    /// Argument expressions (in the *calling* module), bound to the macro's
    /// parameters in order.
    pub args: Vec<ExprId>,
    /// The module the arguments live in (for lowering them).
    pub arg_module: ModuleId,
    /// The macro body's choices, resolved for *this* call site.
    pub body_choices: Box<ChoiceTable>,
    /// Set when the checker resolved the body **accept-lean** (a higher-order
    /// macro whose parameter is a callable passed by name — resolution-doc
    /// §3.7): its body is resolved with the parameter bound only by type, so the
    /// verdict never wrongly rejects.
    pub lean: bool,
    /// The callables passed by bare name to a higher-order (`lean`) macro
    /// (mt-040): each `(param_index, callable)` pair records which func/pred a
    /// callable-by-name argument names, so the lowerer can bind the parameter and
    /// inline `param[args]` as the real call. Empty for ordinary macros; a `lean`
    /// macro with an unresolved callable argument (ambiguous / macro-valued) has
    /// no entry for it, so lowering defers typed rather than guessing.
    pub callables: Vec<(usize, CallableChoice)>,
}

/// A func/pred passed to a higher-order macro by bare name (resolution-doc §3.7,
/// mt-040). The macro body invokes the parameter as `param[args]`; the lowerer
/// binds the parameter to this callable and inlines the call.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CallableChoice {
    /// The resolved func/pred the argument name refers to.
    pub func: FuncId,
    /// Whether the callable is a predicate (its `param[..]`/`param` use is a
    /// formula) rather than a function (a relational value).
    pub is_pred: bool,
}

/// The phase-8 quantifier **ground expansion** (`CompModule.visit(ExprQt)`
/// `:588-633`, mt-107 P2, ADR-0024's P0 addendum).
///
/// `all f: Vertex$.subfields | …` is not a quantifier at all in the reference:
/// it is rewritten, at *resolve* time, into a fold of the body re-resolved once
/// per meta atom with `f` bound to that concrete singleton meta sig. That is why
/// `f.value` is never higher-order — by the time the name `value` resolves, `f`
/// denotes exactly one meta sig and its own `value` relation is the only
/// candidate left.
///
/// mettle's resolver does not rewrite the AST, and [`ChoiceTable`] holds one
/// entry per `(ModuleId, ExprId)`, so N re-resolutions of one body would
/// collide. Each binding therefore gets its **own sibling sub-table** — the
/// shape [`MacroChoice::body_choices`] already uses per call site, here N-wide
/// for one node. The whole record is stamped on the quantifier/comprehension
/// node itself, which carries no other choice.
///
/// **What the lowerer replays (P3).** For each [`MetaBinding`] in order: bind
/// [`Self::var`] to that binding's `atom` (a `one` sig, so a singleton
/// relation), swap the choice table to the binding's `choices`, lower
/// [`Self::body`], and combine with the guard `atom in bound` — where
/// [`Self::bound`] lowers against the **outer** table, once, since the decl
/// bound is resolved exactly once. The three folds are the reference's:
///
/// | [`MetaFold`] | per-binding term | empty fold |
/// |---|---|---|
/// | `All` | `atom in bound implies body` | `true` |
/// | `Some` | `atom in bound and body` | `false` |
/// | `Comprehension` | `(atom in bound and body) implies atom else none` | `none` (arity 1) |
///
/// The reference accumulates each new term on the **left** of what it has so
/// far (`answer = term.and(answer)`), so its tree for atoms `a₁…aₙ` is
/// `tₙ ∘ (tₙ₋₁ ∘ (… ∘ t₁))`; [`Self::bindings`] is in synthesis order (`a₁…aₙ`),
/// which is the order to fold *right-to-left* to reproduce that tree exactly.
/// The operators are associative and commutative, so a left fold agrees on the
/// value — only the emitted term order would differ.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MetaExpansion {
    /// Which of the three expandable binders this was.
    pub fold: MetaFold,
    /// The single bound name, rebound per binding.
    pub var: String,
    /// The decl bound (`Vertex$.subfields`), an [`ExprId`] in the node's own
    /// module. Resolved **once**, into the enclosing table — never per binding.
    pub bound: ExprId,
    /// The body, re-resolved once per binding under that binding's sub-table.
    pub body: ExprId,
    /// One entry per meta atom the guard admitted, in the reference's
    /// `metaSigAtoms()`-then-`metaFieldAtoms()` synthesis order. Empty is a
    /// legal, reachable state — see the empty-fold column above.
    pub bindings: Vec<MetaBinding>,
}

/// Which fold a [`MetaExpansion`] collapses to — the three binders the
/// reference's guard admits (`:585`, `x.op == ALL || SOME || COMPREHENSION`).
/// `no`/`one`/`lone`/`sum` are **not** here: they stay ordinary quantifiers over
/// meta atoms (mt-107 P0 §M2 SURPRISE 2).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum MetaFold {
    /// `all x: … | …` — a conjunction of implications.
    All,
    /// `some x: … | …` — a disjunction of conjunctions.
    Some,
    /// `{ x: … | … }` — a union of guarded singletons.
    Comprehension,
}

/// One binding of a [`MetaExpansion`]: a concrete meta atom and the body's
/// choices *as resolved with the variable bound to it*.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MetaBinding {
    /// The meta sig the variable denotes for this copy of the body. Always a
    /// `one` sig (`S$` or `S$f`), so it denotes exactly one atom.
    pub atom: SigId,
    /// The body's choices for *this* binding. Keyed by the same `(ModuleId,
    /// ExprId)` pairs as its siblings — which is precisely why they cannot be
    /// merged into one table.
    pub choices: Box<ChoiceTable>,
}

/// The choice table: `(ModuleId, ExprId)` → the resolved [`ExprChoice`]. Keyed
/// and iterated in a deterministic order (`BTreeMap`, STYLE D2).
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct ChoiceTable {
    map: BTreeMap<(ModuleId, ExprId), ExprChoice>,
}

impl ChoiceTable {
    /// An empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Records `choice` for `(module, expr)`. Re-resolution of the same node is
    /// deterministic, so a repeat write is a no-op-equivalent overwrite.
    pub fn record(&mut self, module: ModuleId, expr: ExprId, choice: ExprChoice) {
        self.map.insert((module, expr), choice);
    }

    /// The choice recorded for `(module, expr)`, if any.
    #[must_use]
    pub fn get(&self, module: ModuleId, expr: ExprId) -> Option<&ExprChoice> {
        self.map.get(&(module, expr))
    }

    /// Number of recorded choices.
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether the table is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Drains every entry of `other` into `self` (used to lift a sub-context's
    /// choices — e.g. a resolved field bound or fact body — into the world's
    /// table). Deterministic: `other` iterates in key order.
    pub fn extend_from(&mut self, other: ChoiceTable) {
        self.map.extend(other.map);
    }
}
