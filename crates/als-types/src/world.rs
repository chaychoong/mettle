//! The resolved, type-checked world — the output of the Rung-2 resolver
//! (ADR-0008 decision 1). New arenas, typed IDs, no object identity, no
//! `Rc<RefCell>` (decision 2): a `SigId` *is* the resolved sig; its module,
//! parents, and fields are id links.
//!
//! Names are bound, the sig hierarchy is built, and every field/func/pred/
//! fact/assert/command is registered and type-checked. Bounds, universe/atom
//! numbering, CNF, and solving are out of scope (later rungs) — this world
//! stops at "resolved + type-checked + accept verdict".

use als_syntax::ast::{CmdKind, Expect, SigMult};
use als_syntax::{define_id, Arena, Span};

use crate::graph::ModuleId;
use crate::ty::Type;

define_id! {
    /// Index into [`ResolvedWorld::sigs`]. A `SigId` that appears in a
    /// [`Type`] product is always a *primitive* sig (`SigKind::Prim`); subset
    /// sigs contribute their parents' prim types instead (resolution-doc §4.1).
    pub struct SigId;
}

define_id! {
    /// Index into [`ResolvedWorld::fields`].
    pub struct FieldId;
}

define_id! {
    /// Index into [`ResolvedWorld::funcs`] — funcs and preds share one arena
    /// (they share one overload namespace, resolution-doc §3.5).
    pub struct FuncId;
}

define_id! {
    /// Index into [`ResolvedWorld::macros`].
    pub struct MacroId;
}

/// The five builtin sigs seeded into every world (resolution-doc §4.1), as
/// fixed `SigId`s. `iden` is a *constant* (`univ->univ`), not a sig, so it is
/// not here.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Builtins {
    /// `univ` — the top unary sig; every prim sig descends from it.
    pub univ: SigId,
    /// `Int` — the integer-atom sig (`SIGINT`).
    pub int: SigId,
    /// `seq/Int` (`SEQIDX`) — a child of `Int`.
    pub seq_int: SigId,
    /// `String` — the string-atom sig.
    pub string: SigId,
    /// `none` — the empty unary sig (absorbing element).
    pub none: SigId,
}

/// The hierarchy kind of a resolved sig (resolution-doc §3.1).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SigKind {
    /// `extends` sig or a builtin: a primitive sig that can be a column of a
    /// [`Type`] product. `parent` is its single prim parent (`None` only for
    /// `univ`, the root; `none`/`Int`/`String` parent = `univ`).
    Prim {
        /// The single prim parent, or `None` for `univ`.
        parent: Option<SigId>,
    },
    /// `in`/`=` subset sig — possibly multiple parents (resolution-doc §3.1,
    /// probe 29). Never itself a Type column; its `ty` is the parent union.
    Subset {
        /// Parent prim/subset sigs the subset draws from.
        parents: Vec<SigId>,
        /// `=` (exact) vs `in`.
        exact: bool,
    },
}

/// A resolved signature.
#[derive(Clone, PartialEq, Eq, Debug)]
// `abstract`/`var`/`private`/builtin are four independent sig facets, each a
// distinct qualifier the grammar allows in any combination — encoding them as
// anything but four bools would misstate the surface.
#[allow(clippy::struct_excessive_bools)]
pub struct ResolvedSig {
    /// Declared name (the bare label, not qualified).
    pub name: String,
    /// The sig's global label — the exact string the reference names its atoms
    /// after (`Util.tailThis(sig.label)`): the bare name for a root-module sig
    /// (`A`), and the alias path from the root for an opened-module sig
    /// (`foo/Widget`, `a/b/Beta`, `ordering/Ord`). This is what
    /// `als_core::scope` prefixes each atom with (`<qualified_name>$<index>`),
    /// so the universe reads exactly as Alloy prints it. mt-029 widening.
    pub qualified_name: String,
    /// The module instance this sig was declared in.
    pub module: ModuleId,
    /// Span of the declaring `sig`/`enum` name.
    pub span: Span,
    /// Hierarchy kind.
    pub kind: SigKind,
    /// `abstract`.
    pub is_abstract: bool,
    /// The synthetic `abstract` parent of an `enum` declaration (the reference
    /// rejects any explicit scope on it — "cannot set a scope on the enum").
    /// mt-029 widening.
    pub is_enum: bool,
    /// `var` (mutable).
    pub is_var: bool,
    /// `private`.
    pub is_private: bool,
    /// A seeded builtin (`univ`/`Int`/`seq/Int`/`String`/`none`).
    pub is_builtin: bool,
    /// `lone`/`one`/`some` sig multiplicity.
    pub mult: Option<SigMult>,
    /// Fields declared in this sig, in source order.
    pub fields: Vec<FieldId>,
    /// Field groups declared together under a pre-colon `disj` modifier
    /// (`disj a, b: bound`), in source order, each holding the ≥2 [`FieldId`]s
    /// of one such declaration. Their fields are pairwise disjoint per owner
    /// atom; mt-038 lowers each group to the staged `no (f0 & f1) and no
    /// ((f0+f1) & f2) and …` fact (translation-ref §2.5, jar-verified). Empty
    /// for a sig with no `disj`-marked multi-name field declaration.
    pub field_disj_groups: Vec<Vec<FieldId>>,
    /// The sig's appended-fact block body (`sig A { … } { fact }`), if written —
    /// an `ExprId` in this sig's [`Self::module`], resolved with an implicit
    /// `this: A` binding (resolution-doc §3.3). mt-031 lowers it as a fact.
    pub appended_fact: Option<als_syntax::ast::ExprId>,
    /// The unary type this sig denotes as an expression: `{self}` for a prim
    /// sig, the union of parent types for a subset sig (resolution-doc §4.1).
    pub ty: Type,
}

/// A resolved field (resolution-doc §3.4).
// The four flags faithfully mirror independent surface-decl markers
// (`var`/`private`/`= e`/`: disj`); packing them into an enum would invent
// structure the reference doesn't have.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ResolvedField {
    /// Field label.
    pub name: String,
    /// The sig that owns this field.
    pub owner: SigId,
    /// Span of the field declaration.
    pub span: Span,
    /// Full relation type: `owner.ty` product the bound's type
    /// (resolution-doc §3.4).
    pub ty: Type,
    /// `var` (mutable field).
    pub is_var: bool,
    /// `private`.
    pub is_private: bool,
    /// `f = e` defined field (resolved in the later pass).
    pub is_defined: bool,
    /// Post-colon `disj` bound (`f: disj e`, resolution-doc §3.4): distinct
    /// owner atoms map to pairwise-disjoint values. Recorded so the lowerer can
    /// refuse it typed (mt-038; the synthesized fact itself is unpinned —
    /// mt-040) rather than silently under-constrain. Never resolve-visible.
    pub is_bound_disj: bool,
    /// The field's declaration bound expression — an `ExprId` in the owner
    /// sig's module (mt-031 widening). For a non-defined field this is the type
    /// bound (`set A`, `A -> one A`, …) whose multiplicity markers mt-031 turns
    /// into synthesized field facts (translation-ref §2.5); for a **defined**
    /// (`f = e`) field it is `= e` (an [`als_syntax::ast::UnOp::ExactlyOf`]
    /// wrapping the value `e`), which mt-031 lowers as `all this: S | this.f =
    /// e`.
    pub bound: als_syntax::ast::ExprId,
}

/// One parameter of a func/pred (resolution-doc §3.5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Param {
    /// Parameter name.
    pub name: String,
    /// Resolved parameter type (with its declared multiplicity folded away —
    /// only the relational shape matters for typing).
    pub ty: Type,
}

/// A resolved func or pred (resolution-doc §3.5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ResolvedFunc {
    /// Declared name (bare).
    pub name: String,
    /// The module instance this func/pred was declared in.
    pub module: ModuleId,
    /// Span of the declaring name.
    pub span: Span,
    /// A `pred` (return type is `FORMULA`) vs a `fun`.
    pub is_pred: bool,
    /// `private`.
    pub is_private: bool,
    /// Parameters in order (a receiver becomes param index 0).
    pub params: Vec<Param>,
    /// The declared return type (`FORMULA` for a pred).
    pub return_ty: Type,
    /// The return-declaration expression (a `fun`'s bound), for per-call
    /// return-type specialization (the reference's `DeduceType` polymorphism —
    /// `dom[r]: set ((r.univ).univ)` yields a tighter type at each call site).
    /// `None` for preds and receiver-less builtins.
    pub return_decl: Option<als_syntax::ast::ExprId>,
    /// The body expression — an `ExprId` in [`Self::module`] (mt-031 widening).
    /// A pred body is a formula; a fun body a relation/int. mt-031 inlines it at
    /// each call site with parameters bound to the arguments.
    pub body: als_syntax::ast::ExprId,
}

/// A registered top-level `let` macro (resolution-doc §3.7). Stored by
/// reference into its defining file's AST; expansion is textual at typecheck.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ResolvedMacro {
    /// Macro name.
    pub name: String,
    /// The module instance this macro was declared in.
    pub module: ModuleId,
    /// Span of the declaring name.
    pub span: Span,
    /// Parameter names (textual params, no types).
    pub params: Vec<String>,
    /// Macro body expression (in the defining module's AST).
    pub body: als_syntax::ast::ExprId,
    /// `private`.
    pub is_private: bool,
}

/// One explicit per-sig scope clause of a command (`but [exactly] N SIG`),
/// with the target already resolved to a [`SigId`] (mt-029 widening). Range
/// (`N..M`) and increment (`:I`) growth scopes collapse to their starting
/// value `scope` for the static Rung-3 slice; growth/trace scopes are Rung 6.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct CommandScope {
    /// The sig this clause scopes (a user sig, or a builtin like `univ`/`none`
    /// that the translation-time scope check will reject).
    pub sig: SigId,
    /// The starting scope bound `N`.
    pub scope: u32,
    /// `exactly N SIG`.
    pub is_exact: bool,
    /// Span of the scope entry (for the translation-time error caret).
    pub span: Span,
}

/// A resolved command (`run`/`check`, resolution-doc §3.6), carrying the scope
/// data `als_core::scope::compute_universe` needs (mt-029 widening): the
/// overall default, per-sig scopes (targets resolved to [`SigId`]s), and the
/// `int`/`seq`/`String` scalar scopes. The Rung-2 gauge only needed that the
/// command *resolved*; the solvable form starts here.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ResolvedCommand {
    /// Span of the command.
    pub span: Span,
    /// `run` or `check`.
    pub kind: CmdKind,
    /// `label:` prefix, if written (skolem/instance naming, later rungs).
    pub label: Option<String>,
    /// `expect 0|1` annotation (post-solve verdict check + the symmetry-0
    /// coupling of `expect 1`, translation-ref §3/§4.4).
    pub expect: Option<Expect>,
    /// `for N` overall default scope (`None` when unwritten — defaults to 3
    /// only when no per-sig scopes were given either, translation-ref §1.1).
    pub overall: Option<u32>,
    /// `N int` — integer bitwidth (`None` → default 4).
    pub bitwidth: Option<u32>,
    /// `N seq` — maximum sequence length (`None` → derived, translation-ref
    /// §1.1).
    pub maxseq: Option<u32>,
    /// `N String` — the String-atom scope value (`None` → only referenced
    /// literals). A `String` scope must be `exactly` (checked at translation).
    pub maxstring: Option<u32>,
    /// Whether the `String` scope was written `exactly`.
    pub string_exact: bool,
    /// `N steps` — trace length (temporal; captured, Rung 6).
    pub steps: Option<u32>,
    /// Explicit per-sig scopes, in source order.
    pub scopes: Vec<CommandScope>,
    /// Sigs forced to an **exact** scope by something other than an explicit
    /// `exactly` — i.e. `open util/ordering[S]` propagating its `exactly`
    /// parameter (translation-ref §5, `additionalExactScopes`). Empty until
    /// mt-035 (gated on LEDGER-004) populates it; the scope layer already
    /// honors it, so the seam is live.
    pub additional_exact: Vec<SigId>,
    /// The resolved command target (mt-031 widening): the pred/fun to run, the
    /// assert to negate, or the inline block. mt-031 lowers this into the
    /// command formula (translation-ref §2.5(3)).
    pub target: CmdTargetResolved,
}

/// A resolved command target (translation-ref §2.5(3), mt-031 widening).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CmdTargetResolved {
    /// `run p` / `check p` on a named pred/fun: the matching overloads (usually
    /// one). mt-031 inlines the body with parameters **existentially
    /// quantified** over their bounds for a `run` (translation-ref §2.5(3)).
    Named(Vec<FuncId>),
    /// `check a` on a named assert: the assertion body (in `module`), lowered
    /// **negated** for a `check`.
    Assert {
        /// The assertion body formula.
        body: als_syntax::ast::ExprId,
        /// The module the body lives in.
        module: ModuleId,
    },
    /// `run { block }` / `check { block }`: the inline block body (in `module`).
    Block {
        /// The block body formula.
        body: als_syntax::ast::ExprId,
        /// The module the body lives in.
        module: ModuleId,
    },
    /// The target could not be resolved to a single meaning (an over-loaded or
    /// missing name a solvable model never reaches — resolution already rejects
    /// it). mt-031 returns a typed error rather than guessing.
    Unresolved,
}

/// A resolved free `fact` (module fact, resolution-doc §3.3, mt-031 widening).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ResolvedFact {
    /// The module instance this fact was declared in.
    pub module: ModuleId,
    /// Optional fact name (diagnostics/provenance).
    pub name: Option<String>,
    /// Span of the fact paragraph.
    pub span: Span,
    /// The fact body formula (an `ExprId` in [`Self::module`]).
    pub body: als_syntax::ast::ExprId,
}

/// The resolved world: arena-owned sigs, fields, funcs, macros, and commands,
/// plus the builtin handles. Produced by [`crate::resolve`].
#[derive(Debug)]
pub struct ResolvedWorld {
    /// Every resolved sig, builtins first (fixed `SigId`s), then user sigs in
    /// declaration order.
    pub sigs: Arena<SigId, ResolvedSig>,
    /// Every resolved field, in declaration order.
    pub fields: Arena<FieldId, ResolvedField>,
    /// Every resolved func/pred, in declaration order.
    pub funcs: Arena<FuncId, ResolvedFunc>,
    /// Every registered macro.
    pub macros: Arena<MacroId, ResolvedMacro>,
    /// Every resolved command, in source order.
    pub commands: Vec<ResolvedCommand>,
    /// Every free `fact` across every reachable module (mt-031 widening), in
    /// module-then-source order — the goal conjoins them all (translation-ref
    /// §2.5(2)).
    pub facts: Vec<ResolvedFact>,
    /// Resolution choices for every name/spine node (mt-031 widening): the seam
    /// [`crate::choice`] documents, so the lowerer never re-derives §4.4.
    pub choices: crate::choice::ChoiceTable,
    /// Every `util/ordering` module instance in the world (mt-035, LEDGER-004):
    /// the ordered sig plus the private `Ord` sig's `First`/`Next` field
    /// relations the bounds phase pins to exact constants when eligible. Enum
    /// auto-opened orderings land here too (probe T13). Populated last, after
    /// fields exist; identified by the stdlib module's resolved identity, never
    /// by a user alias.
    pub ordering: Vec<OrderingInstance>,
    /// Builtin sig handles (resolution-doc §4.1).
    pub builtins: Builtins,
}

/// One resolved `open util/ordering[S]` instance (mt-035, LEDGER-004 /
/// translation-ref §5). The bounds phase reads this to (a) know `S` is
/// force-exact (also carried command-side by
/// [`ResolvedCommand::additional_exact`]) and (b) pin `first`/`next` to exact
/// constants over `S`'s atoms when `S` has no genuine subsig partition choice.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct OrderingInstance {
    /// The ordered sig `S` (the module's `exactly elem` argument).
    pub elem: SigId,
    /// The private `Ord` sig's `First: set elem` field.
    pub first: FieldId,
    /// The private `Ord` sig's `Next: elem -> elem` field.
    pub next: FieldId,
}

impl ResolvedWorld {
    /// Whether prim sig `sub` is the same as, or a descendant of, prim sig
    /// `sup` (resolution-doc §4.1 `isSameOrDescendentOf`). `none` descends from
    /// everything; `univ` is an ancestor of everything. Walks the prim parent
    /// chain; subset sigs are not valid arguments (they never appear as Type
    /// columns).
    #[must_use]
    pub fn is_same_or_descendent(&self, sub: SigId, sup: SigId) -> bool {
        if sub == sup || sup == self.builtins.univ || sub == self.builtins.none {
            return true;
        }
        if sub == self.builtins.univ || sup == self.builtins.none {
            return false;
        }
        let mut cur = sub;
        loop {
            match &self.sigs[cur].kind {
                SigKind::Prim { parent: Some(p) } => {
                    if *p == sup {
                        return true;
                    }
                    cur = *p;
                }
                // Reached univ (no parent) or an unexpected subset column.
                SigKind::Prim { parent: None } | SigKind::Subset { .. } => return false,
            }
        }
    }

    /// Whether a `this: sub` atom is guaranteed to lie in `sup`'s domain — i.e.
    /// `sub` is the same as or a descendant of `sup` following **both** the prim
    /// `extends` chain **and** subset (`in`/`=`) parents. Unlike
    /// [`Self::is_same_or_descendent`] (a Type-column predicate where subset
    /// sigs never appear), this is the reference's `Sig.isSameOrDescendentOf`
    /// used for the implicit-`this` field visibility check (resolution-doc
    /// §3.3): a field of `Product` is reachable as `this.field` inside a
    /// `sig Dangerous in Product` fact because a `Dangerous` atom *is* a
    /// `Product`.
    #[must_use]
    pub fn sig_is_same_or_descendent(&self, sub: SigId, sup: SigId) -> bool {
        if sub == sup {
            return true;
        }
        match &self.sigs[sub].kind {
            SigKind::Prim { parent: Some(p) } => self.sig_is_same_or_descendent(*p, sup),
            SigKind::Prim { parent: None } => false,
            SigKind::Subset { parents, .. } => parents
                .iter()
                .any(|&p| self.sig_is_same_or_descendent(p, sup)),
        }
    }
}
