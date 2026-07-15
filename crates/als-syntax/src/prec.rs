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
