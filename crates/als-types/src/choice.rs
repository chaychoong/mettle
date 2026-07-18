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
//! Only two surface node families carry a choice:
//! - a bare [`als_syntax::ast::ExprKind::Name`]/`AtName` → a [`NameChoice`];
//! - an application spine ([`als_syntax::ast::ExprKind::Binary`] with
//!   [`als_syntax::ast::BinOp::Join`], or a [`als_syntax::ast::ExprKind::BoxJoin`])
//!   → a [`SpineChoice`].
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
