//! Forbid-mode overflow-guard POLARITY conformance (mt-090): jar-pinned verdicts
//! for translation-ref §10.7f — an `implies` antecedent keeps the implication's
//! own polarity, and neither an antecedent nor an int-ITE is an escape from
//! Defect A (§10.7c rule 4, retracted).
//!
//! Jar-free: every expected verdict is a constant citing its §10.7f probe id
//! (`scratchpad/probe/mt090/p{1,2,3}_jar.txt`, Alloy 6.2.0, sat4j, symmetry 20,
//! `A4Options.noOverflow = true`), so CI runs it with no oracle.
//!
//! Bitwidth is the default 4 (`Int` = −8..7) throughout. Two overflow drivers
//! recur: `#Node` under `for exactly 8 Node` (a translation-CONSTANT overflow
//! with an empty free-variable set) and `#n.r` under `fact { r = Node -> Node }`
//! (8 for every `n`, so it overflows at every binding AND depends on `n`).
//! `plus[n,7] > 7` is raw-false for every non-overflowing `n`, so only the guard
//! can make it true.

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Solves command 0 of `src` in FORBID mode (the LEDGER-001 canonical default).
/// `true` = SAT (a `run` instance or a `check` counterexample), `false` = UNSAT.
/// Panics on a defer: none of these shapes may defer.
fn forbid(src: &str) -> bool {
    solve(src, false)
}

/// [`forbid`]'s allow-mode twin — used only where the allow column is the
/// control that proves the guard is what moved the verdict.
fn allow(src: &str) -> bool {
    solve(src, true)
}

fn solve(src: &str, allow_overflow: bool) -> bool {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let opts = SolveOptions {
        allow_overflow,
        ..SolveOptions::default()
    };
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    match solve_goal(&ir, &scoped, &goal, &bounds, &opts) {
        Ok(SolveVerdict::Sat(_)) => true,
        Ok(SolveVerdict::Unsat) => false,
        Ok(SolveVerdict::Unknown) => panic!("unbudgeted solve returned Unknown"),
        Err(e) => panic!("unexpected defer: {e:?}"),
    }
}

/// `sig Node {}` plus one command, at `exactly 8 Node` so `#Node` = 8 overflows.
fn node8(cmd: &str) -> String {
    format!("open util/integer\nsig Node {{}}\n{cmd} for exactly 8 Node\n")
}

/// `node8` with a total `r`, so `#n.r` = 8 for every `n`.
fn nodes8_with_r(cmd: &str) -> String {
    format!(
        "open util/integer\nsig Node {{ r: set Node }}\n\
         fact Complete {{ r = Node -> Node }}\n{cmd} for exactly 8 Node\n"
    )
}

// ---------------- §10.7f rule P: only `not` flips the guard polarity ---------

#[test]
fn implies_antecedent_keeps_its_own_polarity() {
    // Probes a0/a3/a4/a5 (§10.7f). The driver is the same constant `#Node` in
    // all four; only its syntactic position moves. Bare at positive polarity the
    // guard EXCLUDES (`∧ ¬of`, a0); an `implies` antecedent does NOT flip, so a
    // `run`'s antecedent is still positive (a3 SAT: the antecedent is forced
    // false, the implication holds vacuously) and a `check`'s antecedent is still
    // negative (a4/a5 SAT: the antecedent is forced TRUE, so the consequent
    // `no Node` fails and the assertion has a counterexample).
    assert!(!forbid(&node8("run { #Node < 0 }"))); // a0
    assert!(forbid(&node8("run { #Node < 0 => no Node }"))); // a3
    assert!(forbid(&node8("check { #Node < 0 => no Node }"))); // a4
    assert!(forbid(&node8("check { #Node >= 0 => no Node }"))); // a5, `>=` direction

    // Allow-mode controls: a3/a5 are allow-UNSAT, so the forbid SAT above is the
    // guard's doing and not an artifact of the wrapped value.
    assert!(!allow(&node8("run { #Node < 0 => no Node }")));
    assert!(!allow(&node8("check { #Node >= 0 => no Node }")));
}

#[test]
fn consequent_and_iff_do_not_flip() {
    // Probes a6/a7/a9 (§10.7f) — the negative space of the rule above. A
    // CONSEQUENT inherits the implication's polarity unchanged (it always did),
    // and `iff` never flips either side.
    assert!(!forbid(&node8("run { some Node => #Node < 0 }"))); // a6
    assert!(!forbid(&node8("check { some Node => #Node >= 0 }"))); // a7
    assert!(forbid(&node8("run { (#Node < 0) iff (no Node) }"))); // a9
}

#[test]
fn negation_flips_exactly_once_around_an_antecedent() {
    // Probes a10/g3 (§10.7f). A `not` INSIDE the antecedent flips once (a10), and
    // a `not` wrapped AROUND the whole implication flips the antecedent once
    // (g3) — mettle used to flip twice in both, cancelling the effect.
    assert!(forbid(&node8("check { not (#Node >= 0) => no Node }"))); // a10
    assert!(forbid(&node8("check { not (#Node < 0 => no Node) }"))); // g3

    // a2/a8 controls: a bare `not` and an EVEN antecedent depth are unchanged.
    assert!(!forbid(&node8("run { not (#Node >= 0) }"))); // a2
    assert!(!forbid(&node8("run { (#Node < 0 => no Node) => no Node }"))); // a8
}

#[test]
fn antecedent_rule_is_independent_of_the_operand() {
    // Probes a11/b2 (§10.7f). The antecedent rule is about polarity, not about
    // the driver: it holds when the driver is NOT translation-constant (a11, a
    // non-exact scope makes the overflow a real circuit) and when it depends on
    // the quantified variable (b2 — mt-089's exact `correctChord` shape).
    assert!(forbid(
        "open util/integer\nsig Node {}\ncheck { #Node < 0 => no Node } for 8 Node\n"
    )); // a11
    assert!(forbid(&nodes8_with_r(
        "check { all n: Node | #n.r < 0 => no n }"
    ))); // b2

    // b0/b1/b3/b4 controls: the same sig-∀ driver bare, in a `run` antecedent,
    // and in a consequent — none of which move.
    assert!(!forbid(&nodes8_with_r("run { all n: Node | #n.r < 0 }"))); // b0
    assert!(forbid(&nodes8_with_r(
        "run { all n: Node | #n.r < 0 => no n }"
    ))); // b1
    assert!(!forbid(&nodes8_with_r(
        "check { all n: Node | some n => #n.r >= 0 }"
    ))); // b3
    assert!(!forbid(&nodes8_with_r("check { all n: Node | #n.r >= 0 }"))); // b4
}

// -------- §10.7f rule C: the classifier has no inputs beyond rules 0–3 -------

#[test]
fn bare_int_driver_in_an_antecedent() {
    // Probes c2/c3 (§10.7f). A bare-`Int` ∀ classifies exactly (rule 0), so in a
    // `run` antecedent (still positive) it RESCUES — forcing the antecedent true
    // and the implication false (c2 UNSAT) — while under a `check` the binder's
    // effective kind flips to ∃ and the negative polarity makes it rescue the
    // other way (c3 SAT).
    let ante = "run { all n: Int | plus[n, 7] > 7 => no Node } for exactly 1 Node\n";
    let ante_check = "check { all n: Int | plus[n, 7] > 7 => no Node } for exactly 1 Node\n";
    let pre = "open util/integer\nsig Node {}\n";
    assert!(!forbid(&format!("{pre}{ante}"))); // c2
    assert!(forbid(&format!("{pre}{ante_check}"))); // c3

    // Allow controls: both flip in allow mode, so the guard is what decided.
    assert!(allow(&format!("{pre}{ante}")));
    assert!(!allow(&format!("{pre}{ante_check}")));

    // c0: the classic bare-`Int` rescue (I11) is untouched.
    assert!(forbid(&format!(
        "{pre}run {{ all n: Int | plus[n, 7] >= n }} for exactly 1 Node\n"
    )));
}

#[test]
fn non_bare_int_driver_in_an_antecedent() {
    // Probes c4/c5 (§10.7f). A comprehension domain is Defect A — classified
    // existential regardless of position. c4 (`run`) is the cell whose accidental
    // cancellation invented rule 4 and must NOT move; c5 is its `check` twin,
    // which the cancellation got wrong.
    let pre = "open util/integer\nsig Node {}\n";
    assert!(forbid(&format!(
        "{pre}run {{ all n: {{ x: Int | x > 0 }} | plus[n, 7] > 7 => no Node }} for exactly 1 Node\n"
    ))); // c4
    assert!(forbid(&format!(
        "{pre}check {{ all n: {{ x: Int | x > 0 }} | plus[n, 7] > 7 => no Node }} for exactly 1 Node\n"
    ))); // c5

    // c1/c6 controls: Defect A bare, and a bare-`Int` EXISTENTIAL antecedent.
    assert!(!forbid(&format!(
        "{pre}run {{ all n: {{ x: Int | x >= 0 }} | plus[n, 7] >= n }} for exactly 1 Node\n"
    ))); // c1
    assert!(forbid(&format!(
        "{pre}run {{ some n: Int | plus[n, 7] > 7 => no Node }} for exactly 1 Node\n"
    ))); // c6
}

#[test]
fn a_frame_the_driver_does_not_mention_classifies_nothing() {
    // Probes g6/g7 (§10.7f). `DefCond.isUnivQuant` only consults a bare-`Int`
    // frame whose variable the operand actually mentions; `#Node` mentions none,
    // so the walk falls through to the existential default even with an enclosing
    // `all n: Int`. The verdicts are then a3's and a4's, unchanged by the binder.
    assert!(forbid(&node8(
        "check { all n: Int | #Node < 0 => no Node }"
    ))); // g6
    assert!(forbid(&node8("run { all n: Int | #Node < 0 => no Node }"))); // g7
}

#[test]
fn nested_and_existential_binders_over_an_antecedent() {
    // Probes g0/g1 (§10.7f) — the rule is per-variable and shape-free: an extra
    // enclosing ∀ (g0) and an ∃ binder (g1) leave the antecedent's polarity and
    // the driver's classification exactly as the single-binder cells.
    assert!(forbid(&nodes8_with_r(
        "check { all m: Node | all n: Node | #n.r < 0 => no n }"
    ))); // g0
    assert!(forbid(&nodes8_with_r(
        "check { some n: Node | #n.r < 0 => no n }"
    ))); // g1
}

// -------------- §10.7f: an int-ITE is not an escape either (rule 4) ----------

#[test]
fn int_ite_is_not_an_escape_from_defect_a() {
    // Probes f0/f3/f4/f5 (§10.7f). `#n.r` keeps the ITE a GENUINE int-ITE (both
    // branches are IntExpressions), unlike mt-051's cells where `plus[..]`
    // returns the SET `Int` and the ITE was relational. With a real int-ITE the
    // sig/comprehension ∀ driver is plain Defect A: excluded, not rescued.
    assert!(!forbid(&nodes8_with_r(
        "run { all n: Node | ((some n) => #n.r else 0) > 7 }"
    ))); // f0
    assert!(!forbid(&nodes8_with_r(
        "run { all n: { x: Node | some x } | ((some n) => #n.r else 0) > 7 }"
    ))); // f3

    // The same driver inside an antecedent — where the retracted rule 4 and the
    // retracted polarity flip used to cancel (f4) and where they did not (f5).
    assert!(forbid(&nodes8_with_r(
        "run { all n: Node | ((some n) => #n.r else 0) > 7 => no n }"
    ))); // f4
    assert!(forbid(&nodes8_with_r(
        "check { all n: Node | ((some n) => #n.r else 0) > 7 => no n }"
    ))); // f5

    // f1/f2 controls: the same shapes without the ITE do not move.
    assert!(!forbid(&nodes8_with_r("run { all n: Node | #n.r > 7 }"))); // f1
    assert!(!forbid(&nodes8_with_r(
        "check { all n: Node | ((some n) => #n.r else 0) <= 7 }"
    ))); // f2
}

#[test]
fn int_ite_with_a_constant_driver() {
    // Probes d3/d4 (§10.7f): no binder at all, so only the polarity rule can
    // decide. Bare under a `check` the guard rescues the assertion (d3 UNSAT);
    // moved into an antecedent it still sees negative polarity, so the antecedent
    // is forced true and the assertion breaks (d4 SAT).
    assert!(!forbid(&node8(
        "check { ((some Node) => #Node else 0) >= 0 }"
    ))); // d3
    assert!(forbid(&node8(
        "check { ((some Node) => #Node else 0) < 0 => no Node }"
    ))); // d4
}
