//! Skolemization **connective** conformance (mt-055, translation-ref §10.6).
//! Jar-free and CI-safe: every constant below was produced at authoring time
//! (2026-07-25) by the reference jar via the conform harness
//!
//! ```text
//! cargo build --release -p als-conform
//! ./target/release/conform <probe>.als --symmetry <N> --enumerate exhaustive
//! ```
//!
//! and is asserted here against mettle's own enumeration (STYLE U3 — the tests
//! never call the jar). Probe sources are inline; copies live in
//! `scratchpad/probe/mt055-tso/repro/`.
//!
//! **The rule.** Kodkod's `Skolemizer` (`kodkod/engine/fol2sat/Skolemizer.java`
//! @ `794226dd`) turns skolemization *off for the whole subtree* whenever it
//! descends into
//!
//! ```java
//! // visit(BinaryFormula), line 471
//! if (op==IFF || (negated && op==AND) || (!negated && (op==OR || op==IMPLIES)))
//!     skolemDepth = -1;
//! // visit(NaryFormula), lines 541-542   (unreachable for Alloy goals, see below)
//! case AND : if (negated)  skolemDepth = -1; break;
//! case OR  : if (!negated) skolemDepth = -1; break;
//! ```
//!
//! Skolemizing under a positive `∨` is *semantically* sound — the jar is simply
//! conservative — but a skolem is an extra free relation, so it changes both the
//! enumerated model count and the §16.3 SBP relation order (`$`-names sort
//! first). Conformance therefore requires copying the jar's conservatism.
//!
//! **Only the `BinaryFormula` arm actually fires.** Alloy never hands Kodkod an
//! n-ary `AND`/`OR` for a block or an `and`/`or` chain: `visit(ExprList)`
//! (`TranslateAlloyToKodkod.java:1062-1067`) calls `getSingleFormula`
//! (`:1035-1058`), which folds the conjuncts into a **binary heap of
//! `BinaryFormula` ANDs** (`n == 0 → Formula.TRUE`, `n == 1 → return me` with no
//! AND node built, `n >= 2 → me.and(other)`). The only n-ary node in an Alloy
//! goal is the root `fgoal = Formula.and(formulas)` (`A4Solution.java:1573`),
//! which is always positive — so `visit(NaryFormula)`'s guards never trigger.
//!
//! Three nuances the rule has to respect, each pinned by a control below:
//! - the carve-out for a one-conjunct block is `getSingleFormula`'s `n == 1`
//!   short-circuit — no AND node exists to block at — so an `assert` body reached
//!   through `check` still skolemizes; see
//!   `fo_skolem_conformance::check_noempty_count_matches_jar_561`;
//! - a **negated** `implies` is not blocked (only `!negated && IMPLIES` is);
//! - a formula-valued **if/else** is blocked at *either* polarity, because the
//!   jar's shape is `c.implies(t) and c.not().implies(e)`
//!   (`TranslateAlloyToKodkod.java:776-783`): positive → two positive `IMPLIES`,
//!   negative → a negated `AND`.

use als_core::ir::Ir;
use als_core::{compute_bounds, compute_universe, enumerate, lower_command, SolveOptions};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Exhaustively enumerates command 0 of `src` at `symmetry` and returns the
/// count (the same shape as `sb_conformance::count_at`).
fn count_at(src: &str, symmetry: u32) -> usize {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    let opts = SolveOptions {
        symmetry,
        ..SolveOptions::default()
    };
    enumerate(&ir, &scoped, &goal, &bounds, &opts)
        .expect("enumerate")
        .count()
}

/// Asserts both jar-pinned counts for a probe: SB-20 (the default quotient) and
/// SB-0 (the raw ADR-0002 yardstick, free of any SBP interaction).
fn assert_counts(src: &str, quotiented: usize, raw: usize, what: &str) {
    assert_eq!(count_at(src, 20), quotiented, "{what}: SB-20 count");
    assert_eq!(count_at(src, 0), raw, "{what}: SB-0 count");
}

const AB: &str = "sig A {}\nsig B {}\n";

// -------------------------------------------------------------- controls
// Contexts where the jar DOES skolemize (or already agreed) — these pin that
// the rule is not over-broad.

/// A bare top-level existential skolemizes on both sides: jar **6** / **16**.
#[test]
fn plain_top_level_existential_skolemizes() {
    assert_counts(
        &format!("{AB}run {{ some b: B | b = b }} for 2\n"),
        6,
        16,
        "plain",
    );
}

/// A **positive `and`** leaves skolemization enabled (`negated && AND` is the
/// blocked case, not this one): jar **4** / **12**.
#[test]
fn positive_and_still_skolemizes() {
    assert_counts(
        &format!("{AB}run {{ some A and (some b: B | b = b) }} for 2\n"),
        4,
        12,
        "positive and",
    );
}

/// `iff` was already blocked in mettle and matches the jar: **5** / **10**.
#[test]
fn iff_blocks_skolemization() {
    assert_counts(
        &format!("{AB}run {{ some A iff (some b: B | b = b) }} for 2\n"),
        5,
        10,
        "iff",
    );
}

// ------------------------------------------------------------ the rule

/// A positive `or` blocks skolemization in **both** branches: jar **8** / **15**
/// (mettle counted 22 / 52 while it skolemized `$b` there — the mt-055 tso bug
/// in miniature).
#[test]
fn positive_or_blocks_skolemization() {
    assert_counts(
        &format!("{AB}run {{ some A or (some b: B | b = b) }} for 2\n"),
        8,
        15,
        "positive or",
    );
}

/// The same through a chained (n-ary) `or`: jar **26** / **63** (was 82 / 244).
#[test]
fn nary_or_blocks_skolemization() {
    assert_counts(
        &format!("{AB}sig C {{}}\nrun {{ some A or some C or (some b: B | b = b) }} for 2\n"),
        26,
        63,
        "n-ary or",
    );
}

/// A positive `implies` blocks skolemization in both antecedent and consequent:
/// jar **7** / **13** (was 14 / 28).
#[test]
fn positive_implies_blocks_skolemization() {
    assert_counts(
        &format!("{AB}run {{ some A implies (some b: B | b = b) }} for 2\n"),
        7,
        13,
        "positive implies",
    );
}

/// A **negated** `and` blocks it too — here the effective existential is the
/// `all` under the `not`: jar **7** / **13** (was 14 / 28).
#[test]
fn negated_and_blocks_skolemization() {
    assert_counts(
        &format!("{AB}run {{ not (some A and (all b: B | b in A)) }} for 2\n"),
        7,
        13,
        "negated and",
    );
}

/// An Alloy **block** with ≥ 2 conjuncts is Kodkod's n-ary `AND`, so a negated
/// block blocks skolemization as well: jar **7** / **13** (was 14 / 28).
#[test]
fn negated_multi_conjunct_block_blocks_skolemization() {
    assert_counts(
        &format!("{AB}run {{ not {{ some A\n all b: B | b in A }} }} for 2\n"),
        7,
        13,
        "negated block",
    );
}

/// The same block reached through a `check` (whose body lowers negated): jar
/// **7** / **13** (was 14 / 28).
#[test]
fn check_of_multi_conjunct_block_blocks_skolemization() {
    assert_counts(
        &format!("{AB}check {{ some A\n all b: B | b in A }} for 2\n"),
        7,
        13,
        "check block",
    );
}

/// A formula-valued **if/else** at positive polarity: the jar emits
/// `c.implies(then) and c.not().implies(else)`, i.e. two **positive `IMPLIES`**
/// nodes, so the condition and both branches are all blocked. Jar **4** at SB-20
/// (probe `scratchpad/probe/mt055-tso/review/ite_pos.als`, `InstProbe` at
/// `symmetry=20`/`noOverflow`/sat4j; its instance dump carries no `$b`). mettle
/// minted `$b` and `$b_2` here before mt-055. Only the SB-20 count is asserted
/// because only that one is jar-pinned.
#[test]
fn positive_if_else_blocks_skolemization_in_both_branches() {
    let src = format!(
        "{AB}run {{ some A implies (some b: B | b = b) else (some b: B | b in A) }} for 2\n"
    );
    assert_eq!(count_at(&src, 20), 4, "positive if/else: SB-20 count");
}

/// The same shape under `check` (negative polarity): the jar's conjunction is now
/// a **negated `AND`**, which blocks just as hard. Jar **6** at SB-20 (probe
/// `review/ite_neg.als`).
#[test]
fn negative_if_else_blocks_skolemization_in_both_branches() {
    let src = format!(
        "{AB}check {{ some A implies (all b: B | b in A) else (all b: B | no b) }} for 2\n"
    );
    assert_eq!(count_at(&src, 20), 6, "negative if/else: SB-20 count");
}

// ---- mt-056: a formula-valued `let` decides polarity at the USE ------------
//
// Alloy's `visit(ExprLet)` translates the RHS once and *places that node at each
// use*; Kodkod's `Skolemizer` is a separate later pass over the assembled tree.
// So the connective rule above is decided at the **use**, not at the binding.
// mettle used to lower the RHS eagerly at the `let`'s own polarity, freezing the
// decision — over-counting where a use was blocked, and UNDER-counting where the
// jar mints one skolem per use.
//
// Cells jar-measured at mt-056 with `scratchpad/probe/mt056/SkolemProbe.java`
// (`A4Solution.getAllSkolems()` + exhaustive count, sat4j, noOverflow, both
// symmetries) over `m1_lets.als` / `m2_capture.als`. The decisive property is
// that every `let` row equals its INLINE twin, so each test asserts the pair.

/// Pins one `let` shape against the inline spelling of the same shape *and*
/// against the jar's measured figures at both symmetries.
#[track_caller]
fn let_matches_inline(
    let_body: &str,
    inline_body: &str,
    raw_count: usize,
    broken_count: usize,
    cell: &str,
) {
    let l = format!("{AB}run {{ {let_body} }} for 2\n");
    let i = format!("{AB}run {{ {inline_body} }} for 2\n");
    assert_eq!(count_at(&l, 0), raw_count, "{cell}: let SB-0");
    assert_eq!(count_at(&i, 0), raw_count, "{cell}: inline SB-0");
    assert_eq!(count_at(&l, 20), broken_count, "{cell}: let SB-20");
    assert_eq!(count_at(&i, 20), broken_count, "{cell}: inline SB-20");
}

const E: &str = "(some b: B | b = b)";

#[test]
fn formula_let_is_transparent_in_every_connective_context() {
    // s01–s09. The `let` must land on the same count as writing the RHS inline,
    // context by context — bare and `and` skolemize (16/6, 12/4), the four
    // blocking connectives do not (15/8, 13/7, 7/5, 10/5).
    let_matches_inline(&format!("let p = {E} | p"), E, 16, 6, "s01 bare");
    let_matches_inline(
        &format!("let p = {E} | p or some A"),
        &format!("{E} or some A"),
        15,
        8,
        "s02 positive or",
    );
    let_matches_inline(
        &format!("let p = {E} | some A or p"),
        &format!("some A or {E}"),
        15,
        8,
        "s03 positive or, other side",
    );
    let_matches_inline(
        &format!("let p = {E} | not p"),
        &format!("not {E}"),
        4,
        3,
        "s04 not",
    );
    let_matches_inline(
        &format!("let p = {E} | p and some A"),
        &format!("{E} and some A"),
        12,
        4,
        "s05 positive and",
    );
    let_matches_inline(
        &format!("let p = {E} | some A implies p"),
        &format!("some A implies {E}"),
        13,
        7,
        "s06 positive implies, consequent",
    );
    let_matches_inline(
        &format!("let p = {E} | p implies some A"),
        &format!("{E} implies some A"),
        13,
        7,
        "s07 positive implies, antecedent",
    );
    let_matches_inline(
        &format!("let p = {E} | not (p and some A)"),
        &format!("not ({E} and some A)"),
        7,
        5,
        "s08 negated and",
    );
    let_matches_inline(
        &format!("let p = {E} | p iff some A"),
        &format!("{E} iff some A"),
        10,
        5,
        "s09 iff",
    );
    let_matches_inline(
        &format!("let p = {E} | all x: A | p"),
        &format!("all x: A | {E}"),
        13,
        7,
        "s10 under a universal",
    );
}

#[test]
fn each_use_of_a_formula_let_skolemizes_independently() {
    // d01 is the cell that refutes any "the shared node is skolemized once"
    // reading: `p and p` mints TWO skolems in the jar (`$…_b` and `$…_b'`) and
    // counts 24/9 — where mettle, reusing one lowered formula, counted 16.
    // d02 (`p or p`) blocks both uses instead, 12/6.
    let_matches_inline(
        &format!("let p = {E} | p and p"),
        &format!("{E} and {E}"),
        24,
        9,
        "d01 two skolemizable uses",
    );
    let_matches_inline(
        &format!("let p = {E} | p or p"),
        &format!("{E} or {E}"),
        12,
        6,
        "d02 two blocked uses",
    );
}

#[test]
fn mixed_contexts_are_decided_per_use_not_by_visit_order() {
    // m01/m02/m03: one skolemizable use and one blocked use, in BOTH orders.
    // The jar mints exactly one skolem and counts 16/6 either way — identical to
    // the unshared inline twins, so there is no first-visit-wins memoisation in
    // Kodkod's `Skolemizer` (the corner mt-056 was told to settle before
    // choosing a design; it is settled: per use, independently).
    let_matches_inline(
        &format!("let p = {E} | p and (p or some A)"),
        &format!("{E} and ({E} or some A)"),
        16,
        6,
        "m01 unblocked then blocked",
    );
    let_matches_inline(
        &format!("let p = {E} | (p or some A) and p"),
        &format!("({E} or some A) and {E}"),
        16,
        6,
        "m02 blocked then unblocked",
    );
    // m05/m06: the same, with the blocked use being a universal body.
    let_matches_inline(
        &format!("let p = {E} | p and (all x: A | p)"),
        &format!("{E} and (all x: A | {E})"),
        16,
        6,
        "m05 bare then under-all",
    );
    let_matches_inline(
        &format!("let p = {E} | (all x: A | p) and p"),
        &format!("(all x: A | {E}) and {E}"),
        16,
        6,
        "m06 under-all then bare",
    );
    // m04: both uses blocked; n03: blocked two different ways.
    let_matches_inline(
        &format!("let p = {E} | (p or some A) and (some B or p)"),
        &format!("({E} or some A) and (some B or {E})"),
        12,
        6,
        "m04 both blocked",
    );
    let_matches_inline(
        &format!("let p = {E} | (all x: A | p) and (p or some A)"),
        &format!("(all x: A | {E}) and ({E} or some A)"),
        12,
        6,
        "n03 blocked at two depths",
    );
}

#[test]
fn a_let_bound_to_another_let_is_transparent_too() {
    // n01: `let q = p` re-binds a formula-`let`; the use of `q` under a positive
    // `or` is still blocked, 15/8 — the same as s02.
    let src = format!("{AB}run {{ let p = {E} | let q = p | q or some A }} for 2\n");
    assert_eq!(count_at(&src, 0), 15, "n01 SB-0");
    assert_eq!(count_at(&src, 20), 8, "n01 SB-20");
}

#[test]
fn the_filed_repro_matches_the_jar() {
    // `scratchpad/probe/mt055-tso/review/let_or.als`, the cell mt-056 was filed
    // on: jar 12/6, mettle 48/… before the fix.
    let src = "sig A {}\nsig B {}\nrun { let p = (some b: B | b in A) | p or some A } for 2\n";
    assert_eq!(count_at(src, 0), 12, "filed repro SB-0");
    assert_eq!(count_at(src, 20), 6, "filed repro SB-20");
}

#[test]
fn per_use_lowering_does_not_capture_a_shadowed_name() {
    // m2_capture c01/c04/c05 — the hazard the per-use design creates and the
    // reason the RHS is re-lowered under the BINDING site's binder stack. The
    // jar translates the RHS once, so its `x` is the OUTER one: c01 must equal
    // the outer-x hand spelling (26/13), NOT the captured one (20/10).
    const AR: &str = "sig A { r: set A }\n";
    let shadowed = format!(
        "{AR}run {{ some x: A | (let p = (some b: A | b in x.r) | all x: A | p) }} for 2\n"
    );
    let outer_hand =
        format!("{AR}run {{ some x: A | (all y: A | (some b: A | b in x.r)) }} for 2\n");
    let captured_hand =
        format!("{AR}run {{ some x: A | (all x: A | (some b: A | b in x.r)) }} for 2\n");
    assert_eq!(count_at(&shadowed, 0), 26, "c01 shadowed SB-0");
    assert_eq!(count_at(&outer_hand, 0), 26, "c04 outer reading SB-0");
    assert_eq!(count_at(&captured_hand, 0), 20, "c05 captured reading SB-0");
    assert_eq!(count_at(&shadowed, 20), 13, "c01 shadowed SB-20");
    assert_eq!(count_at(&outer_hand, 20), 13, "c04 outer reading SB-20");
    assert_eq!(
        count_at(&captured_hand, 20),
        10,
        "c05 captured reading SB-20"
    );
    // c06: shadowing AND a blocked use at once — 36/18.
    let both = format!(
        "{AR}run {{ some x: A | (let p = (some b: A | b in x.r) | all x: A | (p or some A)) }} for 2\n"
    );
    assert_eq!(count_at(&both, 0), 36, "c06 SB-0");
    assert_eq!(count_at(&both, 20), 18, "c06 SB-20");
}
