//! Translation-cache conformance (mt-137, ADR-0029, LEDGER-017): jar-pinned
//! verdicts for the shapes where the reference reaches ONE translated formula
//! node twice and its polarity-blind `FOL2BoolCache` hands the second reach the
//! first visit's overflow guard.
//!
//! Every cell below is verbatim from a banked probe file, and every expected
//! verdict is the Alloy 6.2.0 jar's, quoted in the comment beside it — so CI runs
//! with no oracle and no JVM:
//!
//! - `scratchpad/probe/mt128/x5_g5.als` (jar column `x5_g5_jar.txt`)
//! - `scratchpad/probe/mt128/x6_g5sharing.als` (`x6_g5sharing_jar.txt`)
//! - `scratchpad/probe/mt137/j1_boundary.als` (`j1_boundary_jar.txt`)
//!
//! The rule the cells pin, in one line: sharing is by **node identity**, its only
//! formula-level producers are a `let` binding and a **zero-parameter** pred call,
//! the reused value is the whole first-visit translation whichever polarity that
//! visit was at, and an occurrence the skolemizer rewrote stops sharing.
//!
//! Each model runs at `exactly 8 Node` with the default bitwidth 4, where `#Node`
//! is 8 and therefore overflows — which is what makes the guard direction, and so
//! the cache's polarity blindness, observable at all. In **allow** mode overflow
//! wraps and no guard is minted, so every allow column is a control: it must not
//! move either.

use als_core::bounds::Bounds;
use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, self_check, solve_goal, Instance, LoweredGoal,
    ScopedUniverse, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// SAT/UNSAT for command `idx` of `src`. `allow` selects the probe harness's
/// "allow" column (`--allow-overflow`); `false` is the "forbid" column, which is
/// mettle's and the jar's default.
fn verdict(src: &str, idx: usize, allow: bool) -> bool {
    matches!(solved(src, idx, allow), Solved::Sat(_))
}

/// One solved command, keeping what a self-check needs.
enum Solved {
    Sat(Box<SatCase>),
    Unsat,
}

struct SatCase {
    ir: Ir,
    scoped: ScopedUniverse,
    goal: LoweredGoal,
    instance: Instance,
    bounds: Bounds,
    opts: SolveOptions,
}

fn solved(src: &str, idx: usize, allow: bool) -> Solved {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[idx]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let opts = SolveOptions {
        allow_overflow: allow,
        ..SolveOptions::default()
    };
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx).expect("lower");
    match solve_goal(&ir, &scoped, &goal, &bounds, &opts).expect("solve") {
        SolveVerdict::Sat(instance) => Solved::Sat(Box::new(SatCase {
            ir,
            scoped,
            goal,
            instance,
            bounds: bounds.bounds,
            opts,
        })),
        SolveVerdict::Unsat => Solved::Unsat,
        // No budget set, so `Unknown` is unreachable.
        SolveVerdict::Unknown => unreachable!("unbudgeted solve returned Unknown"),
    }
}

// ======================= mt-128 wave 5: `scratchpad/probe/mt128/x5_g5.als` ===

/// The g5 corner and the controls that separate "shared node reused across
/// polarity" from "a let-bound FORMULA is translated once", verbatim.
const X5_G5: &str = "\
sig Node {}
sig Cell {}
run g5_let_shared      { let p = (#Node < 0) | p or (not p) } for exactly 8 Node, exactly 0 Cell
run g5_dup_shared      { (#Node < 0) or (not (#Node < 0)) } for exactly 8 Node, exactly 0 Cell
run g5_let_shared_ite  { let p = (#Node < 0) | (p => (some Node) else (some Node)) } for exactly 8 Node, exactly 0 Cell
run g5_let_pos_only    { let p = (#Node < 0) | p } for exactly 8 Node, exactly 0 Cell
run g5_let_neg_only    { let p = (#Node < 0) | not p } for exactly 8 Node, exactly 0 Cell
run g5_let_and         { let p = (#Node < 0) | p and (not p) } for exactly 8 Node, exactly 0 Cell
";

#[test]
fn x5_g5_let_shared_reuses_the_positive_visits_guard() {
    // cmd[0] g5_let_shared | jar allow=SAT forbid=SAT.
    // The whole feature in one cell: the two uses of `p` are one node, the first
    // visit is positive, and the negated use gets that translation verbatim — so
    // the excluded middle is NOT a tautology under the guard and the command is
    // satisfiable even with overflow forbidden.
    assert!(verdict(X5_G5, 0, true));
    assert!(verdict(X5_G5, 0, false));
}

#[test]
fn x5_dup_shared_is_not_syntactic_sharing() {
    // cmd[1] g5_dup_shared | jar allow=SAT forbid=UNSAT.
    // Two separately-written occurrences of the same text are two AST nodes, so
    // nothing is shared: each is translated at its own polarity and the excluded
    // middle survives as a tautology. This is the cell that rules out structural
    // (hash-consing) sharing as the mechanism.
    assert!(verdict(X5_G5, 1, true));
    assert!(!verdict(X5_G5, 1, false));
}

#[test]
fn x5_let_shared_ite_is_unmoved() {
    // cmd[2] g5_let_shared_ite | jar allow=SAT forbid=SAT.
    // The formula-ITE desugaring already reaches ONE lowered condition at both
    // polarities, so mettle matched here before classes existed; it must not move.
    assert!(verdict(X5_G5, 2, true));
    assert!(verdict(X5_G5, 2, false));
}

#[test]
fn x5_single_use_lets_are_unmoved() {
    // cmd[3] g5_let_pos_only | jar allow=SAT forbid=UNSAT.
    // cmd[4] g5_let_neg_only | jar allow=UNSAT forbid=UNSAT.
    // One use is one member: the class is dropped and the guard is the use's own.
    assert!(verdict(X5_G5, 3, true));
    assert!(!verdict(X5_G5, 3, false));
    assert!(!verdict(X5_G5, 4, true));
    assert!(!verdict(X5_G5, 4, false));
}

#[test]
fn x5_let_and_stays_contradictory() {
    // cmd[5] g5_let_and | jar allow=UNSAT forbid=UNSAT.
    // Sharing makes `p and (not p)` `X ∧ ¬X` for one X — still unsatisfiable. The
    // cell guards against a class turning a contradiction into a model.
    assert!(!verdict(X5_G5, 5, true));
    assert!(!verdict(X5_G5, 5, false));
}

// ================ mt-128 wave 6: `scratchpad/probe/mt128/x6_g5sharing.als` ===

/// Does the corner need literal AST-node sharing, or only a `let`? Verbatim.
const X6_SHARING: &str = "\
sig Node {}
sig Cell {}
pred P { #Node < 0 }
run h1_let_or_neg_first { let p = (#Node < 0) | (not p) or p } for exactly 8 Node, exactly 0 Cell
run h2_two_lets { let p = (#Node < 0) | let q = (#Node < 0) | p or (not q) } for exactly 8 Node, exactly 0 Cell
run h3_pred_twice { P or (not P) } for exactly 8 Node, exactly 0 Cell
run h4_let_same_pol { let p = (#Node < 0) | p or p } for exactly 8 Node, exactly 0 Cell
run h5_let_nested_neg { let p = (#Node < 0) | not (p and (not p)) } for exactly 8 Node, exactly 0 Cell
";

#[test]
fn x6_negative_first_visit_wins_too() {
    // cmd[0] h1_let_or_neg_first | jar allow=SAT forbid=SAT.
    // First-visit-wins in either direction: here the FIRST reach is the negated
    // one, and the positive use inherits its guard.
    assert!(verdict(X6_SHARING, 0, true));
    assert!(verdict(X6_SHARING, 0, false));
}

#[test]
fn x6_two_lets_binding_identical_text_do_not_share() {
    // cmd[1] h2_two_lets | jar allow=SAT forbid=UNSAT.
    // Two `let`s are two binding instances, hence two classes of one member each:
    // both dissolve, and nothing is shared. Sharing is by node, not by text.
    assert!(verdict(X6_SHARING, 1, true));
    assert!(!verdict(X6_SHARING, 1, false));
}

#[test]
fn x6_zero_parameter_pred_called_twice_shares() {
    // cmd[2] h3_pred_twice | jar allow=SAT forbid=SAT.
    // The jar's `cacheForConstants` keeps one translated node per zero-parameter
    // `Func`, so two ExprCall nodes reach one translation.
    assert!(verdict(X6_SHARING, 2, true));
    assert!(verdict(X6_SHARING, 2, false));
}

#[test]
fn x6_same_polarity_reuse_is_observationally_neutral() {
    // cmd[3] h4_let_same_pol | jar allow=SAT forbid=UNSAT.
    // Both uses are positive, so sharing changes the circuit but not the verdict.
    assert!(verdict(X6_SHARING, 3, true));
    assert!(!verdict(X6_SHARING, 3, false));
}

#[test]
fn x6_sharing_survives_an_enclosing_negation() {
    // cmd[4] h5_let_nested_neg | jar allow=SAT forbid=SAT.
    // `not (p and (not p))`: the two uses sit at opposite polarities under an
    // outer negation, and the class still reuses the first visit.
    assert!(verdict(X6_SHARING, 4, true));
    assert!(verdict(X6_SHARING, 4, false));
}

// ============= mt-137 wave 1: `scratchpad/probe/mt137/j1_boundary.als` ======

/// The sharing boundary: which callees cache, how wide the guard family is, and
/// where skolemization severs. Verbatim.
const J1_BOUNDARY: &str = "\
sig Node {}
pred P0 { #Node < 0 }
pred P1[m: Int] { #Node < m }
pred P2[s: set Node] { #s < 0 }
fun F0: Int { #Node }
run j1_zeroparam { P0 or (not P0) } for exactly 8 Node
run j2_intparam { P1[0] or (not P1[0]) } for exactly 8 Node
run j3_setparam { P2[Node] or (not P2[Node]) } for exactly 8 Node
run j4_let_mult { let p = (some (#Node)) | p or (not p) } for exactly 8 Node
run j5_let_quant { let p = (some n: Node | #Node < 0) | p or (not p) } for exactly 8 Node
run j6_let_quant_and { let p = (some n: Node | #Node < 0) | p and (not p) } for exactly 8 Node
run j7_neg_first { (not P0) or P0 } for exactly 8 Node
run j8_fun_int { (F0 < 0) or (not (F0 < 0)) } for exactly 8 Node
";

#[test]
fn j1_zero_parameter_pred_call_shares() {
    // cmd[0] j1_zeroparam | jar allow=SAT forbid=SAT.
    assert!(verdict(J1_BOUNDARY, 0, true));
    assert!(verdict(J1_BOUNDARY, 0, false));
}

#[test]
fn j2_j3_any_parameter_severs_the_call_cache() {
    // cmd[1] j2_intparam | jar allow=SAT forbid=UNSAT.
    // cmd[2] j3_setparam | jar allow=SAT forbid=UNSAT.
    // `cacheForConstants` is consulted only when `f.count() == 0`. One parameter
    // bypasses it — even with the *identical* argument at both call sites — so
    // each call re-translates into fresh nodes and nothing is shared. This is the
    // cell that scopes the whole feature to zero-parameter callees.
    assert!(verdict(J1_BOUNDARY, 1, true));
    assert!(!verdict(J1_BOUNDARY, 1, false));
    assert!(verdict(J1_BOUNDARY, 2, true));
    assert!(!verdict(J1_BOUNDARY, 2, false));
}

#[test]
fn j4_the_reused_guard_family_is_wider_than_int_comparison() {
    // cmd[3] j4_let_mult | jar allow=SAT forbid=SAT.
    // `some (#Node)` is a multiplicity test over an `Int[..]`-derived operand, so
    // the guard is minted in the matrix layer rather than at an int comparison —
    // and it too rides along with the first visit.
    assert!(verdict(J1_BOUNDARY, 3, true));
    assert!(verdict(J1_BOUNDARY, 3, false));
}

#[test]
fn j5_a_whole_quantified_formula_is_shared() {
    // cmd[4] j5_let_quant | jar allow=SAT forbid=SAT.
    // Both occurrences sit under a positive `or`, where the skolemizer is blocked,
    // so the shared node survives and the entire quantified translation is reused.
    // mettle re-lowers the RHS per use and allocates a FRESH bound variable each
    // time, so this is also the cell that pins the class validator's
    // alpha-equivalence: compare those copies by raw `VarId` and the class would
    // dissolve here.
    assert!(verdict(J1_BOUNDARY, 4, true));
    assert!(verdict(J1_BOUNDARY, 4, false));
}

#[test]
fn j6_skolemization_severs_sharing() {
    // cmd[5] j6_let_quant_and | jar allow=UNSAT forbid=UNSAT.
    // Under `and`, the first occurrence is a positive top-level existential and
    // the skolemizer rewrites it while the negated one stays blocked. The copies
    // then differ structurally — one names a skolem relation the other does not —
    // and the class dissolves, which is the jar's post-skolem cache. Without the
    // validator's by-id relation comparison this cell would flip to SAT.
    assert!(!verdict(J1_BOUNDARY, 5, true));
    assert!(!verdict(J1_BOUNDARY, 5, false));
}

#[test]
fn j7_pred_call_sharing_is_first_visit_wins_in_either_direction() {
    // cmd[6] j7_neg_first | jar allow=SAT forbid=SAT.
    assert!(verdict(J1_BOUNDARY, 6, true));
    assert!(verdict(J1_BOUNDARY, 6, false));
}

#[test]
fn j8_zero_parameter_fun_sharing_is_polarity_clean() {
    // cmd[7] j8_fun_int | jar allow=SAT forbid=UNSAT.
    // A zero-parameter `fun` shares at the Expression/Int level, where the cached
    // value carries no guard direction; the two comparisons around it are distinct
    // formula nodes. So a fun mints no class, and this stays a tautology.
    assert!(verdict(J1_BOUNDARY, 7, true));
    assert!(!verdict(J1_BOUNDARY, 7, false));
}

// ================================ coherence =================================

#[test]
fn a_shared_instance_satisfies_its_own_goal() {
    // The evaluator must share a class's first visit exactly as the encoder does.
    // Without that it stays polarity-correct, judges `p or (not p)` a tautology,
    // and rejects the very instance the encoder newly accepts — so every cell
    // above would ship with a self-check failure behind it.
    let src = "sig Node {}\nrun { let p = (#Node < 0) | p or (not p) } for exactly 8 Node\n";
    let Solved::Sat(case) = solved(src, 0, false) else {
        panic!("g5_let_shared must be SAT in forbid mode (jar: SAT)");
    };
    assert!(
        !case.goal.trans_classes.is_empty(),
        "the shared `let` must have produced a surviving translation class"
    );
    if let Err(failure) = self_check(
        &case.ir,
        &case.scoped,
        &case.goal,
        &case.instance,
        &case.opts,
        &case.bounds,
    ) {
        panic!("self-check rejected a class-shared instance: {failure}");
    }
}

#[test]
fn class_minting_is_deterministic() {
    // Classes are minted in lowering order and validated by a fixed traversal, so
    // two lowerings of one command must produce the identical table — the memo
    // keys downstream are only as deterministic as this (STYLE D1).
    let src = "sig Node {}\nrun { let p = (#Node < 0) | p or (not p) } for exactly 8 Node\n";
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");

    let table = |()| {
        let mut ir = Ir::default();
        let bounds = compute_bounds(&world, &scoped, &mut ir);
        lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0)
            .expect("lower")
            .trans_classes
    };
    let first = table(());
    assert_eq!(first.len(), 2, "both uses of `p` join one class");
    assert_eq!(first, table(()));

    // And the verdict itself is stable across repeated solves.
    assert!(verdict(src, 0, false));
    assert!(verdict(src, 0, false));
}
