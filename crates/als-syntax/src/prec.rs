//! The single source of truth for Alloy 6 operator binding powers
//! (grammar-doc section 3, the 21-level precedence table).
//!
//! Both the [`crate::parser`] (which consumes these numbers in its Pratt loop
//! and prefix gates) and the [`crate::print`] pretty-printer (which maps each
//! AST node back to its tier to place minimal parentheses) read the *same*
//! constants and mapping functions here, so the two can never drift apart —
//! the printer's parens are correct by construction against the parser's
//! precedence, not against a hand-copied second table.
//!
//! Binding powers are Pratt-style: an infix operator with `(lbp, rbp)` is
//! consumed by `parse_operand(min)` only while `lbp >= min`, and recurses into
//! its right operand at `rbp`. Left-associative tiers use `lbp < rbp`;
//! right-associative tiers use `lbp > rbp`. Prefix operators bind their
//! operand at a fixed power and carry a *tier* — the loosest operand slot in
//! which they may legally appear.

use crate::ast::{BinOp, CmpOp, Mult};

/// Prefix binding power (tier and operand power) for `!`/`not` and the unary
/// temporal connectives — looser than comparisons (`!a = b` ≡ `!(a = b)`),
/// tighter than `&&`.
pub(crate) const BP_NOT: u8 = 16;
/// Prefix operand power for the set tests `no some lone one set seq` — they
/// bind a shift-level operand, so `no a = b` ≡ `(no a) = b`.
pub(crate) const BP_TEST: u8 = 20;
/// *Tier* of the set tests: they sit at the comparison level, so they may
/// open the operand of anything looser than a comparison (`! no a`,
/// `a until no b`) but not a comparison's own right operand (`x in one A` is
/// jar-rejected) nor their own operand (`no no a` is jar-rejected — hence
/// tier < [`BP_TEST`]).
pub(crate) const TIER_TEST: u8 = 18;
/// Prefix binding power for `# sum int` — tighter than `+`, so `#a + b` ≡
/// `(#a) + b`.
pub(crate) const BP_NUMUNOP: u8 = 26;
/// Right binding power of `=>`/`else` (right-assoc, dangling-else).
pub(crate) const BP_IMPLIES_R: u8 = 10;
/// Prefix binding power for the closure operators `~ ^ *` and the tier of the
/// postfix prime `'` — tighter than dot/box join, looser than an atom.
pub(crate) const BP_PRIME_CLOSURE: u8 = 42;
/// A binding power no operator reaches: an atom (or any fully self-delimited
/// node) never needs parentheses, so its exposed edges use this.
pub(crate) const BP_ATOM: u8 = u8::MAX;

/// Left/right binding power of the `->` arrow (with or without
/// multiplicities) — right-associative (`A->B->C` ≡ `A->(B->C)`).
pub(crate) const ARROW_BP: (u8, u8) = (33, 32);
/// Left/right binding power of a comparison (`= in < > <= >=`, negated or
/// not) — left-associative and chainable.
pub(crate) const CMP_BP: (u8, u8) = (18, 19);
/// Left/right binding power of the `.`/`[...]` join tier — left-associative,
/// tighter than every classified infix operator.
pub(crate) const JOIN_BP: (u8, u8) = (40, 41);

/// Binding powers of every [`BinOp`] (grammar-doc section 3).
///
/// Total over the enum so the printer can key on any binary node; the parser
/// reaches these through [`crate::parser`]'s `classify_infix`. `Implies`,
/// `Join`, and `Seq` never come back from `classify_infix` (they are built by
/// dedicated parser paths) but appear as [`BinOp`] nodes the printer must
/// place, so their powers live here too.
pub(crate) fn binary_bp(op: BinOp) -> (u8, u8) {
    match op {
        // Formula sequencing `;` — the weakest tier, right-associative.
        BinOp::Seq => (3, 2),
        BinOp::Or => (6, 7),
        BinOp::Iff => (8, 9),
        BinOp::Implies => (11, BP_IMPLIES_R),
        BinOp::And => (12, 13),
        BinOp::Until | BinOp::Releases | BinOp::Since | BinOp::Triggered => (14, 15),
        BinOp::Shl | BinOp::Sha | BinOp::Shr => (20, 21),
        BinOp::Union | BinOp::Diff | BinOp::IntAdd | BinOp::IntSub => (22, 23),
        BinOp::IntMul | BinOp::IntDiv | BinOp::IntRem => (24, 25),
        BinOp::Override => (28, 29),
        BinOp::Intersect => (30, 31),
        BinOp::Join => JOIN_BP,
        BinOp::DomRestrict => (34, 35),
        BinOp::RanRestrict => (36, 37),
    }
}

/// Binding powers of a comparison node (all [`CmpOp`]s share one tier).
pub(crate) fn cmp_bp(_op: CmpOp) -> (u8, u8) {
    CMP_BP
}

/// Binding powers of an arrow node with the given multiplicities (all
/// annotations share the one arrow tier).
pub(crate) fn arrow_bp(_lhs: Option<Mult>, _rhs: Option<Mult>) -> (u8, u8) {
    ARROW_BP
}

// -- Binder-composition budget (mt-014 Part 2) -----------------------------
//
// Grammar-doc section 3.1 says a binder may be the rightmost operand of "any
// operator below" level 2, but the reference's LALR grammar does not let
// that compose freely across MULTIPLE enclosing operators the way a naive
// uniformly-recursive implementation (mt-011/mt-013) does. Jar-verified over
// ~220 probes (docs/reference/fuzzing.md section 2; LIMITATIONS.md): a
// binder may be absorbed as the rightmost operand of exactly ONE enclosing
// operator "hop"; a second hop is rejected UNLESS the enclosing operator is
// a bare `implies` (`=>` with no `else`) or the `else` branch of
// `implies … else`, either of which grants a fresh two-hop budget to its own
// branch. Comparisons (`= in < > <= >= …`) never accept a binder as their
// operand at all, at any budget (the set-test prefixes `no some lone one set
// seq` are equally hard-blocked, but that gate lives in
// `crate::parser::parse_prefix` -- there is no printer-side equivalent since
// those prefixes never themselves *have* a right-hand binder operand to
// re-print through this table).
//
// This lives here, not in `parser.rs`, for exactly the reason the rest of
// this module does (see the module doc): the parser enforces this budget
// and the printer must independently re-derive the *same* answer (does this
// position need parens around a binder?) to stay round-trip-safe. A single
// shared function is the only way the two can never drift.

/// `TOP` marks a fresh expression start (may itself be a bare binder, and
/// grants the generous two-hop budget to whichever operator it meets); `HOP`
/// marks one ordinary operator's own rightmost operand (may itself be a bare
/// binder, but grants NO further budget to a nested operator); `NONE` means
/// a bare binder is not allowed here at all.
pub(crate) const BINDER_BUDGET_NONE: u8 = 0;
pub(crate) const BINDER_BUDGET_HOP: u8 = 1;
pub(crate) const BINDER_BUDGET_TOP: u8 = 2;

/// How an enclosing infix operator affects the binder-composition budget of
/// its right operand -- the only three classes [`child_binder_budget`]
/// distinguishes (every operator not named here, including `Arrow`/`Join`,
/// is [`BinderOperator::Ordinary`]).
#[derive(Clone, Copy)]
pub(crate) enum BinderOperator {
    /// `=>` with no trailing `else` (or the `else` branch of `implies …
    /// else`) -- refreshes the budget to `TOP`.
    Implies,
    /// A comparison (`= in < > <= >= …`, negated or not) -- hard-blocks a
    /// binder operand regardless of the ambient budget.
    Comparison,
    /// Every other infix operator (`or iff and until… + - & -> <: :> .` …).
    Ordinary,
}

/// The budget an infix operator's own right operand receives, given the
/// ambient budget of the call that is about to consume it. Only a `TOP`
/// ambient budget grants anything; every operator gets one ordinary `HOP`
/// except `implies` (refreshed to `TOP`, jar-verified) and comparisons
/// (hard `NONE`, jar-verified — comparisons sit at grammar-doc's tier 9
/// alongside the set-test prefixes, which are equally hard-blocked in
/// `crate::parser::parse_prefix`).
pub(crate) fn child_binder_budget(budget: u8, op: BinderOperator) -> u8 {
    if budget < BINDER_BUDGET_TOP {
        return BINDER_BUDGET_NONE;
    }
    match op {
        BinderOperator::Implies => BINDER_BUDGET_TOP,
        BinderOperator::Comparison => BINDER_BUDGET_NONE,
        BinderOperator::Ordinary => BINDER_BUDGET_HOP,
    }
}

/// The budget a *prefix* operator's own operand receives (mt-026 refinement
/// to mt-014 Part 2's over-permissive "every ordinary prefix is transparent"
/// claim — jar-verified 2026-07-16 against 427 fresh probes,
/// `docs/reference/fuzzing.md` section 2). A prefix (`!`/`not`/the temporal
/// unaries/`# int sum`/the closure operators `~ ^ *`; the set-test prefixes
/// `no some lone one set seq` are separately hard-blocked and never call
/// this) passes its ambient budget through **unchanged only while that
/// ambient budget is already `TOP`** — chained arbitrarily deep, still
/// `TOP` (`! ! ! all x: A | …`, `always always always all x: A | …` both
/// parse). But once the ambient budget has already been spent down to `HOP`
/// by an enclosing ordinary infix operator's one hop, a prefix does *not*
/// forward that `HOP` to a binder beneath it — collapses to `NONE` instead,
/// jar-rejected (`q and always all x: A | …`, `q and not some x: A | …`,
/// `r + ~ all x: A | …`, `q or # all x: A | …`, `q until ~ all x: A | …` —
/// every ordinary infix tier, every prefix whose own tier gate admits it at
/// that position, every binder kind, uniformly) even though the
/// un-prefixed bare binder in the exact same slot is fine
/// (`q and all x: A | …`). `implies`'s refreshed `TOP` branches are
/// unaffected (a prefix there still sees `TOP`, so still transparent).
pub(crate) fn prefix_operand_budget(budget: u8) -> u8 {
    if budget >= BINDER_BUDGET_TOP {
        budget
    } else {
        BINDER_BUDGET_NONE
    }
}
