//! The resolved, type-checked world — the output of the Rung-2 resolver
//! (ADR-0008 decision 1). New arenas, typed IDs, no object identity, no
//! `Rc<RefCell>` (decision 2): a `SigId` *is* the resolved sig; its module,
//! parents, and fields are id links.
//!
//! Names are bound, the sig hierarchy is built, and every field/func/pred/
//! fact/assert/command is registered and type-checked. Bounds, universe/atom
//! numbering, CNF, and solving are out of scope (later rungs) — this world
//! stops at "resolved + type-checked + accept verdict".

use als_syntax::ast::{CmdKind, SigMult};
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
    /// The module instance this sig was declared in.
    pub module: ModuleId,
    /// Span of the declaring `sig`/`enum` name.
    pub span: Span,
    /// Hierarchy kind.
    pub kind: SigKind,
    /// `abstract`.
    pub is_abstract: bool,
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
    /// The unary type this sig denotes as an expression: `{self}` for a prim
    /// sig, the union of parent types for a subset sig (resolution-doc §4.1).
    pub ty: Type,
}

/// A resolved field (resolution-doc §3.4).
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

/// A resolved command (`run`/`check`, resolution-doc §3.6). The Rung-2 gauge
/// only needs that it *resolved*; the solvable form is a later rung.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ResolvedCommand {
    /// Span of the command.
    pub span: Span,
    /// `run` or `check`.
    pub kind: CmdKind,
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
    /// Builtin sig handles (resolution-doc §4.1).
    pub builtins: Builtins,
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
}
