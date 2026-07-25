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
