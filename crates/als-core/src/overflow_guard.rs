//! The forbid-mode overflow-guard classifier (translation-ref §10.7c) — shared
//! by the encoder ([`crate::encode`]) and the evaluator ([`crate::eval`]) so the
//! two implementations apply an identical guard.
//!
//! The jar's `DefCond.isUnivQuant` walk recognizes a quantifier binder as
//! **universal** for the Milicevic/Jackson rescue only when its domain is
//! *literally* the bare `Int`/`seq/Int` builtin; a `sig` or comprehension domain
//! fails the same `isInt()` string check and defaults to **existential**
//! (over-excludes instead of rescues — the common `all p: Sig | <overflow over p>`
//! shape, §10.7c rule 0/GAP2a). This is a purely **per-variable** rule: a
//! variable classifies by ITS OWN binder domain only, with **no dependence on
//! nesting shape, depth, or type** ("Defect B" — a supposed nesting-position
//! defect — was **retracted** in §10.7c/§10.7d round 3: its decisive probes were
//! all confounded by `negate[8]` silently emptying conjunction-shaped domains).
//!
//! ## The one-sided `Int[·]`-cast shape at `=`/`in`/mult-tests (§10.7c ext, mt-051)
//! A relational comparison (`RelCompare`) or multiplicity test (`MultTest`) whose
//! set-operator structure contains an overflow-capable `Int[·]` cast is governed
//! by two jar-pinned effects (probe labels in `scratchpad/probe/mt051_report.md`):
//!
//! - **(A) cast value semantics** — the jar builds every `IntToExprCast` cell with
//!   `Int.eq(other, Environment.empty())` (`∧ ¬accumOverflow`), so in forbid mode
//!   an overflowed cast denotes the **empty** set, polarity-independent, in every
//!   context. This lives at the `IntToAtom` node in both back ends.
//! - **(B) comparison-level guard** — `BooleanMatrix.eq/subset/some` additionally
//!   thread `DefCond.ensureDef`, i.e. the same rules 0–3 classification below is
//!   applied to each capable cast reachable through the compared sides' set
//!   structure ([`collect_capable_casts`]), **unless** the cast's overflow flag is
//!   translation-constant ([`translation_constant`]) — a constant-empty matrix
//!   sheds its `DefCond` in the jar's matrix fast paths, so (B) is lost while (A)
//!   still fires (the R-cardun/T5/T6 constant-escape trio).
//!
//! ## Rule 4 (the int-ITE / `implies`-antecedent sliver) — RETRACTED (mt-090)
//! §10.7f. There is no escape. The jar's `Environment.negate()` fires only in
//! `FOL2BoolTranslator.visit(NotFormula)`, so an `implies` **antecedent** keeps
//! the implication's own polarity, and `DefCond.isUnivQuant` never consults the
//! surrounding operator at all. mt-051's supporting cells were confounded twice
//! over: the antecedent cells cancelled a wrong polarity against a wrong
//! classification, and the "int-ITE" cells were relational ITEs over `Int[·]`
//! casts (`plus[..]` is a `fun` returning the SET `Int`), i.e. FACT-2/FACT-4
//! machinery, not a classification escape. Probes f0/f3/f4 — genuine int-ITEs
//! over `#·` branches — refute the escape directly.

use std::collections::BTreeSet;

use crate::bounds::Bounds;
use crate::ir::{
    CompDecl, FormulaKind, IntExprId, IntExprKind, Ir, RelConst, RelExprId, RelExprKind, VarId,
};

/// The shift-amount mask width `⌈log2 w⌉` = `32 − leading_zeros(w−1)` (Kodkod
/// `TwosComplementInt`, translation-ref §10.7d): only the low `mask` bits of a
/// shift amount are consulted for the value. Shared by the encoder circuit and
/// the evaluator so both mask identically.
pub(crate) fn shift_mask_width(w: usize) -> usize {
    if w <= 1 {
        0
    } else {
        (usize::BITS - (w - 1).leading_zeros()) as usize
    }
}

/// One enclosing quantifier binder on the path to a comparison (innermost last).
#[derive(Clone, Copy, Debug)]
pub(crate) struct QuantFrame {
    /// The bound variable.
    pub var: VarId,
    /// Whether the quantifier's domain is literally the `Int`/`seq/Int` builtin
    /// (the only domain the jar's classifier recognizes as universal).
    pub bare_int: bool,
    /// The binder's **effective** kind after polarity normalization.
    pub effective_forall: bool,
}

/// Whether an integer literal is outside the bitwidth's two's-complement range,
/// i.e. whether Kodkod's `IntConstant` for it carries a **constantly-TRUE**
/// overflow flag (translation-ref §10.7k, mt-101). `8` at bitwidth 4 wraps
/// silently to the Int atom `-8` on the value layer, but the flag it raises is
/// what `DefCond.ensureDef` then folds into the enclosing comparison.
pub(crate) fn const_overflows(value: i32, bitwidth: u32) -> bool {
    value < crate::lower::int_min(bitwidth) || value > crate::lower::int_max(bitwidth)
}

/// Whether an integer expression can overflow — it syntactically contains
/// arithmetic, `sum`, or cardinality, **or is a literal outside the bitwidth's
/// range** (not an in-range `Const`, not `int[·]`; translation-ref §10.7c,
/// §10.7k). Drives both the value semantics and the comparison-level guard.
pub(crate) fn overflow_capable(ir: &Ir, bitwidth: u32, id: IntExprId) -> bool {
    match &ir.int_exprs[id].kind {
        IntExprKind::Const(v) => const_overflows(*v, bitwidth),
        IntExprKind::AtomToInt(_) => false,
        IntExprKind::Card(_)
        | IntExprKind::Neg(_)
        | IntExprKind::Binary { .. }
        | IntExprKind::Sum { .. } => true,
        IntExprKind::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => {
            overflow_capable(ir, bitwidth, *then_branch)
                || overflow_capable(ir, bitwidth, *else_branch)
        }
    }
}

/// Collects every **overflow-capable** `Int[·]` cast reachable through the
/// SET-OPERATOR structure of a relational expression (translation-ref §10.7c
/// ext (B), mt-051): recurse through relational `Binary` (union/intersect/diff/
/// join/product/override), `Unary`, and `IfThenElse` branches — but **not** into
/// `Formula` positions (an ITE condition, a comprehension body: those guard at
/// their own comparison sites) nor into the int expr beneath a cast (a
/// nested-inside-`Card` cast is a documented out-of-scope corner). Pushed in
/// traversal order so the caller's lhs-then-rhs walk is deterministic (STYLE D2).
///
/// **The union corner is UNPINNED and deliberately left over-guarding**
/// (translation-ref §10.7h, mt-096). The jar sheds the guard for some
/// union-nested casts (`(plus[n,7] + 3) = 3` under a comprehension-∀ is jar SAT,
/// probes k4/k16/u1) but keeps it for others that differ only in context
/// (`plus[F.v,7] + 1 in Int` with no quantifier is jar UNSAT, probe t4c — the
/// mt-051 T1/T4 cells, re-confirmed at mt-096) or only in the sibling operand (a
/// union of TWO capable casts guards, probes u11/v3, while a sibling that cannot
/// actually overflow sheds, probe v1). No predicate over the IR separates all of
/// {u1, t4c, v1, v3, u11, v9}, so mettle keeps descending — the CONSERVATIVE
/// direction, which never turns a jar UNSAT into a mettle SAT. Every other
/// former is jar-confirmed to keep the guard (intersection u2/u5, difference f4,
/// if-then-else f6/f7, join f8, override u16, product u17).
pub(crate) fn collect_capable_casts(
    ir: &Ir,
    bitwidth: u32,
    id: RelExprId,
    out: &mut Vec<IntExprId>,
) {
    match &ir.rel_exprs[id].kind {
        RelExprKind::IntToAtom(ie) => {
            if overflow_capable(ir, bitwidth, *ie) {
                out.push(*ie);
            }
        }
        RelExprKind::Binary { lhs, rhs, .. } => {
            collect_capable_casts(ir, bitwidth, *lhs, out);
            collect_capable_casts(ir, bitwidth, *rhs, out);
        }
        RelExprKind::Unary { expr, .. } => collect_capable_casts(ir, bitwidth, *expr, out),
        RelExprKind::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => {
            collect_capable_casts(ir, bitwidth, *then_branch, out);
            collect_capable_casts(ir, bitwidth, *else_branch, out);
        }
        // Leaves and Formula-bearing nodes stop the set-structure walk.
        RelExprKind::Relation(_)
        | RelExprKind::Var(_)
        | RelExprKind::Const(_)
        | RelExprKind::Comprehension { .. }
        | RelExprKind::Prime(_) => {}
    }
}

/// Whether a cast operand's overflow flag is **translation-constant** (§10.7c ext
/// (C), mt-051): its int-expr subtree contains no `Var` reference and no `Sum`
/// node, and every relation it references (through `Card`/`int[·]`, etc.) is
/// **exactly** bound (`lower == upper`). Such a cast contributes NO
/// comparison-level (B) guard — the jar's constant-empty matrices shed their
/// `DefCond` — while its (A) value semantics still applies (R-cardun/T5/T6). The
/// SAME predicate runs in the encoder and the evaluator, so the two can never
/// drift (do NOT substitute `Bool::Const`-ness on the encoder side).
pub(crate) fn translation_constant(ir: &Ir, bounds: &Bounds, id: IntExprId) -> bool {
    match &ir.int_exprs[id].kind {
        // Every literal is translation-constant, in range or not. An
        // OUT-OF-RANGE one makes the cast matrix constant-EMPTY, and the jar's
        // matrix fast paths shed a constant-empty operand's `DefCond` on exactly
        // the formers/readers §10.7k measures — which is why the (B) escape
        // stays unconditional here and the residual is pinned, not implemented.
        IntExprKind::Const(_) => true,
        IntExprKind::Card(rel) | IntExprKind::AtomToInt(rel) => rel_const(ir, bounds, *rel),
        IntExprKind::Neg(ie) => translation_constant(ir, bounds, *ie),
        IntExprKind::Binary { lhs, rhs, .. } => {
            translation_constant(ir, bounds, *lhs) && translation_constant(ir, bounds, *rhs)
        }
        // A `Sum` binder makes the operand non-constant regardless of its body.
        IntExprKind::Sum { .. } => false,
        IntExprKind::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => {
            formula_const(ir, bounds, *cond)
                && translation_constant(ir, bounds, *then_branch)
                && translation_constant(ir, bounds, *else_branch)
        }
    }
}

/// [`translation_constant`] over a relation expression: no `Var`, and every
/// referenced free relation is exactly bound.
fn rel_const(ir: &Ir, bounds: &Bounds, id: RelExprId) -> bool {
    match &ir.rel_exprs[id].kind {
        RelExprKind::Relation(r) => bounds.get(*r).is_some_and(|b| b.lower() == b.upper()),
        // A quantifier/comprehension variable is never a translation constant.
        RelExprKind::Var(_) => false,
        // `none`/`univ`/`iden` are fixed functions of the universe.
        RelExprKind::Const(RelConst::None | RelConst::Univ | RelConst::Iden) => true,
        RelExprKind::Binary { lhs, rhs, .. } => {
            rel_const(ir, bounds, *lhs) && rel_const(ir, bounds, *rhs)
        }
        RelExprKind::Unary { expr, .. } | RelExprKind::Prime(expr) => rel_const(ir, bounds, *expr),
        RelExprKind::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => {
            formula_const(ir, bounds, *cond)
                && rel_const(ir, bounds, *then_branch)
                && rel_const(ir, bounds, *else_branch)
        }
        RelExprKind::Comprehension { decls, body } => {
            decls
                .iter()
                .all(|d: &CompDecl| rel_const(ir, bounds, d.bound))
                && formula_const(ir, bounds, *body)
        }
        RelExprKind::IntToAtom(ie) => translation_constant(ir, bounds, *ie),
    }
}

/// [`translation_constant`] over a formula (reached only through an ITE
/// condition or a comprehension body): no `Var`/`Sum`, exact relations only.
fn formula_const(ir: &Ir, bounds: &Bounds, id: crate::ir::FormulaId) -> bool {
    match &ir.formulas[id].kind {
        FormulaKind::Const(_) => true,
        FormulaKind::Not(f) => formula_const(ir, bounds, *f),
        FormulaKind::And(parts) | FormulaKind::Or(parts) => {
            parts.iter().all(|&p| formula_const(ir, bounds, p))
        }
        FormulaKind::Implies {
            antecedent,
            consequent,
        } => formula_const(ir, bounds, *antecedent) && formula_const(ir, bounds, *consequent),
        FormulaKind::Iff(l, r) => formula_const(ir, bounds, *l) && formula_const(ir, bounds, *r),
        FormulaKind::RelCompare { lhs, rhs, .. } => {
            rel_const(ir, bounds, *lhs) && rel_const(ir, bounds, *rhs)
        }
        FormulaKind::IntCompare { lhs, rhs, .. } => {
            translation_constant(ir, bounds, *lhs) && translation_constant(ir, bounds, *rhs)
        }
        FormulaKind::MultTest { expr, .. } => rel_const(ir, bounds, *expr),
        // A quantifier binds a variable — its body is not a translation
        // constant; the lasso loop atom is a free solver variable (mt-066).
        FormulaKind::Quant { .. } | FormulaKind::LoopIs { .. } => false,
        FormulaKind::TemporalUnary { body, .. } => formula_const(ir, bounds, *body),
        FormulaKind::TemporalBinary { lhs, rhs, .. } => {
            formula_const(ir, bounds, *lhs) && formula_const(ir, bounds, *rhs)
        }
    }
}

/// Classifies one overflowing operand at a comparison (translation-ref §10.7c's
/// operational rule list), returning `forall_dep` = whether it classifies as
/// depending on an effective-∀ (a **rescue**) rather than an existential (an
/// **exclude**). `frames` is the enclosing-quantifier stack (innermost last);
/// `free` is the operand's free-variable set.
///
/// This is `DefCond.isUnivQuant` verbatim in behavior, and it has **no other
/// inputs**: neither an `implies` antecedent nor an int-ITE is an escape
/// (§10.7f, mt-090 — the old rule 4 is retracted).
pub(crate) fn classify(frames: &[QuantFrame], free: &BTreeSet<VarId>) -> bool {
    // The single per-variable rule (§10.7c rules 0–3): classify by the innermost
    // enclosing binder whose domain is bare `Int`/`seq/Int` and whose variable the
    // operand depends on — a bare-`Int` ∀ rescues, a bare-`Int` ∃ excludes. No
    // bare-`Int` binder ⇒ Defect A defaults the classification to **existential**
    // (exclude), regardless of nesting shape/depth/type.
    frames
        .iter()
        .rev()
        .find(|f| f.bare_int && free.contains(&f.var))
        .is_some_and(|f| f.effective_forall)
}
