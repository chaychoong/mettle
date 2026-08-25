//! Overflow-guard **shedding** conformance (mt-129 pinned the rule, mt-130
//! implemented it): jar-pinned verdicts for which `Int[·]` casts still deliver a
//! comparison-level guard once the jar's matrix folding has had its say.
//!
//! Every cell below is one command of `scratchpad/probe/mt129/s1_mechanism.als`,
//! `s2_adversarial.als` or `s3_implementation.als` (labels preserved verbatim),
//! measured against the Alloy 6.2.0 jar with `A4Options.noOverflow` set
//! explicitly per cell, sat4j, symmetry 0. Raw jar output sits beside each model
//! in `*_jar.txt`; the mechanism, with Kodkod line numbers, is in that
//! directory's `NOTES.md`. Both overflow columns are asserted: `allow` is the
//! internal control, and an allow/forbid split IS a guard.
//!
//! **The rule** (`overflow_guard.rs`, translation-ref §10.7e–§10.7k):
//!
//! * **(R-a)** an `Int[e]` cast whose overflow circuit folds to the constant
//!   `TRUE` — every integer leaf constant *after quantifier ground substitution*,
//!   and the arithmetic overflows or divides by zero — is a matrix with **zero
//!   cells** that still carries a live overflow circuit;
//! * **(R-b)** a binary, left-associative UNION drops the circuit of a
//!   cells-empty operand, testing the **left** one first; OVERRIDE runs the same
//!   test on its **right** operand only; every other former merges
//!   unconditionally;
//! * **(R-c)** `lone`/`one` over a cells-empty matrix and `some` over one holding
//!   a constant-`TRUE` cell answer before the guard and shed it; `no`, `in`, `=`
//!   never shed; `#` merges the matrix circuit, `sum` never sees it.
//!
//! Cells are grouped by what they defend. **Group A** was already agreeing before
//! mt-130 and pins the negative space — the formers and readers that must keep
//! guarding. **Group B** is the 26 cells mt-129 measured as divergent; each one
//! moved to AGREE with this bead, including the six that were jar UNSAT against a
//! mettle SAT (b2/b3/b5/a6/f3/h1), the direction mt-096 asserted could not occur.

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Solve command 0 of `src`; `true` = allow overflow, `false` = forbid.
/// `Ok(true)` = SAT, `Ok(false)` = UNSAT — no cell here may defer.
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
        Err(e) => panic!("cell must not defer: {e:?}"),
    }
}

/// Asserts one cell's `(allow, forbid)` pair, naming the probe label on failure.
fn cell(label: &str, src: &str, allow: bool, forbid: bool) {
    assert_eq!(solve(src, true), allow, "{label} allow");
    assert_eq!(solve(src, false), forbid, "{label} forbid");
}

/// The `s1_mechanism.als` preamble, verbatim. Every wave-1 cell was measured with
/// all four sigs present, so the tests reproduce the same universe.
fn s1(body: &str) -> String {
    format!(
        "open util/integer\n\
         sig Node {{}}\n\
         one sig Q {{ h: Int -> Int }}\n\
         fact DiagQ {{ Q.h = {{a: Int, b: Int | a = b}} }}\n\
         one sig K {{ z: one Int }}\n\
         fact ForceK {{ K.z > 6 }}\n\
         one sig H {{ u: one Int }}\n\
         fact FixH {{ H.u = 7 }}\n\
         run {{ {body} }} for 3 but 4 int\n"
    )
}

/// An `s1` cell under the wave-1 comprehension-∀ over `1..7`, where `plus[n,7]`
/// overflows at every binding.
fn s1q(body: &str) -> String {
    s1(&format!("all n: {{x: Int | x>=1 and x<=7}} | {body}"))
}

/// The `s2_adversarial.als` / `s3_implementation.als` preamble.
fn s23(body: &str) -> String {
    format!("open util/integer\nsig Node {{}}\nrun {{ {body} }} for 3 but 4 int\n")
}

/// An `s2`/`s3` cell under the same comprehension-∀.
fn s23q(body: &str) -> String {
    s23(&format!("all n: {{x: Int | x>=1 and x<=7}} | {body}"))
}

// ===========================================================================
// GROUP A — cells that agreed BEFORE mt-130 and must not regress.
// ===========================================================================

#[test]
fn group_a_union_keeps_the_guard_when_the_left_operand_has_cells() {
    // a2/a4/a8: the mirror images of group B's a1/a3/a7. `BooleanMatrix.or`
    // tests the LEFT operand first, so an empty LEFT hands the result the
    // RIGHT's circuit — and the RIGHT is the cast. Same commutative operator,
    // opposite verdict. (a8's left operand is `Int - Int`, whose cells fold
    // away in the factory: `x ∧ ¬x` is FALSE.)
    cell("a2", &s1q("(none + plus[n,7]) in Int"), true, false);
    cell("a4", &s1q("no (none + plus[n,7])"), false, false);
    cell("a8", &s1q("((Int - Int) + plus[n,7]) in Int"), true, false);
}

#[test]
fn group_a_a_union_of_two_capable_casts_keeps_the_guard() {
    // g1/g3/j1: when BOTH operands are cells-empty the left test wins, and the
    // result is the RIGHT's clone — which carries the RIGHT's live circuit. So
    // doubling a cast does not shed it.
    cell("g1", &s1q("(plus[n,7] + plus[n,1]) in Int"), true, false);
    cell(
        "g3",
        &s1q("(none + (plus[n,7] + plus[n,7])) in Int"),
        true,
        false,
    );
    cell(
        "j1",
        &s23q("(plus[n,7] + plus[n,7] + plus[n,7]) in Int"),
        true,
        false,
    );
}

#[test]
fn group_a_intersection_and_difference_keep_the_guard() {
    // `and`/`difference` merge the operands' `DefCond` BEFORE any emptiness
    // test, so the flag survives even though the value is empty. c3/d4/d5/d6
    // (intersection) and f2/f4/f5 (difference).
    cell("c3", &s1q("(plus[n,K.z] & Int) in Int"), true, false);
    cell("d4", &s1q("not no (plus[n,7] & Int)"), true, false);
    cell("d5", &s1q("not lone (plus[n,7] & Int)"), false, false);
    cell("d6", &s1q("one (plus[n,7] & Int)"), true, false);
    cell("f2", &s1q("(3 - plus[n,7]) in Int"), true, false);
    cell("f4", &s1q("lone (3 - plus[n,7])"), true, false);
    cell("f5", &s1q("no (3 - plus[n,7])"), false, false);
}

#[test]
fn group_a_join_product_transpose_and_ite_keep_the_guard() {
    // i7 (transpose over a product) is the mt-129 cell; the join (mt-096 f8r1)
    // and the two if-then-else formers (mt-096 f6r1/f7r1) are the mt-096 cells
    // the same collector still has to descend. All four: allow SAT, forbid
    // UNSAT — a real guard.
    cell(
        "i7",
        &s23q("~(plus[n,7] -> 3) in (Int -> Int)"),
        true,
        false,
    );
    let join = "open util/integer\none sig P { g: Int -> Int }\n\
         fact Diag { P.g = {a: Int, b: Int | a = b} }\n\
         run { all n: {x: Int | x>=1 and x<=7} | (plus[n,7]).(P.g) in Int } for 3 but 4 int\n";
    cell("f8r1", join, true, false);
    cell(
        "f6r1",
        &s23q("(n>0 => plus[n,7] else 0) in Int"),
        true,
        false,
    );
    cell(
        "f7r1",
        &s23q("(n<=0 => 0 else plus[n,7]) in Int"),
        true,
        false,
    );
}

#[test]
fn group_a_the_ground_no_quantifier_union_still_sheds() {
    // b1/b4/b6/b7 — mt-129's group B, the cells that show the shedding is about
    // GROUNDNESS, not about the enclosing quantifier: with no quantifier at all
    // a constant overflowing cast still folds to a cells-empty matrix, and the
    // union/`lone` fast paths still drop its circuit. These already agreed,
    // via mettle's old blanket constant escape; they must keep agreeing now that
    // the escape is gone and the union rule carries them.
    cell("b1", &s1("(plus[7,7] + 3) in Int"), true, true);
    cell("b4", &s1("lone (plus[7,7] & Int)"), true, true);
    cell("b6", &s1("(plus[7,7] + none) in Int"), true, true);
    cell("b7", &s1("(plus[7,7] + 3) = 3"), false, true);
}

#[test]
fn group_a_a_symbolic_cast_keeps_the_guard() {
    // c1/c2/c5/c6: spell the `7` as a fact-pinned field and the overflow circuit
    // is a GATE, not a constant — the matrix has cells, nothing sheds. c6 is the
    // probe that shows the jar's `Simplifier` does not fold `H.u = 7` into a
    // constant bound either.
    cell("c1", &s1q("(plus[n,K.z] + 3) in Int"), true, false);
    cell("c2", &s1q("plus[n,K.z] in Int"), true, false);
    cell("c5", &s1("(plus[K.z,7] + 3) in Int"), true, false);
    cell("c6", &s1q("(plus[n,H.u] + 3) in Int"), true, false);
}

#[test]
fn group_a_the_bare_int_domain_classification_is_unchanged() {
    // h2/h3/h4/h5/h6: `DefCond.isUnivQuant` recognizes only a literally-`Int`
    // domain as universal, where KEEPING the guard is TRUE-ward. mt-130 changes
    // WHICH casts reach the classifier, never the classification itself.
    cell(
        "h2",
        &s23("all n: Int | some (none + plus[n,7])"),
        true,
        true,
    );
    cell("h3", &s23q("some (none + plus[n,7])"), true, false);
    cell("h4", &s23q("some (plus[n,7] + none)"), true, false);
    cell("h5", &s23("all n: Int | some plus[n,7]"), true, true);
    cell("h6", &s23q("some plus[n,7]"), true, false);
}

#[test]
fn group_a_a_guarded_nonempty_operand_is_not_the_one_dropped() {
    // i1/i2/i4/i6: it is the EMPTY operand's flag that goes, not "the left one".
    // `3 - plus[n,7]` is guarded AND non-empty (cell `3` stays constant-TRUE),
    // so a `none` on either side of it drops nothing.
    cell("i1", &s23q("(none + (3 - plus[n,7])) in Int"), true, false);
    cell("i2", &s23q("((3 - plus[n,7]) + none) in Int"), true, false);
    let partial = s23(&format!(
        "all n: {{x: Int | x>=0 and x<=7}} | {}",
        "plus[n,1] in Int"
    ));
    cell("i4", &partial, true, false);
    cell(
        "i6",
        &s23q("((none + plus[n,7]) & Int) in Int"),
        true,
        false,
    );
}

#[test]
fn group_a_the_trigger_is_the_circuit_and_a_bare_one_still_guards() {
    // k6/k7: div-by-zero raises the same constantly-TRUE circuit `plus` does, and
    // a bare cast (k6) or one on the RIGHT of a union (k7) keeps its guard.
    cell("k6", &s23q("div[n,0] in Int"), true, false);
    cell("k7", &s23q("(none + div[n,0]) in Int"), true, false);
}

#[test]
fn group_a_cardinality_over_a_shed_union_carries_no_flag() {
    // a5: `#` merges the MATRIX's circuit — but the union already dropped the
    // empty LEFT operand's, so there is nothing to merge. The control for group
    // B's a6, which is the same cell with the operands swapped.
    cell("a5", &s1q("#(plus[n,7] + none) >= 0"), true, true);
}

// ===========================================================================
// GROUP B — the 26 cells mt-129 measured as DIVERGENT; all now agree.
// ===========================================================================

#[test]
fn group_b_union_is_left_first_and_therefore_asymmetric() {
    // a1/a3/a7 (jar SAT, mettle was UNSAT): the cast is the LEFT operand and it
    // is cells-empty, so `or` returns the RIGHT's clone and the circuit is gone.
    // Pair these with group A's a2/a4/a8 — same operator, operands swapped.
    cell("a1", &s1q("(plus[n,7] + none) in Int"), true, true);
    cell("a3", &s1q("no (plus[n,7] + none)"), false, true);
    cell("a7", &s1q("(plus[n,7] + (Int - Int)) in Int"), true, true);
}

#[test]
fn group_b_a_ground_overflowing_cast_is_still_guarded() {
    // b2/b3/b5 — three of the six cells that were jar UNSAT against a mettle
    // SAT, i.e. the direction mt-096's "conservative" rationale said could not
    // occur. They are mettle's old unconditional constant escape, now deleted:
    // with no union/override fast path and no short-circuiting reader in the way,
    // a fully ground overflowing cast delivers its guard. b2 is the cheapest
    // witness in the whole matrix — no quantifier, no union, no field.
    cell("b2", &s1("plus[7,7] in Int"), true, false);
    cell("b3", &s1("(plus[7,7] & Int) in Int"), true, false);
    cell("b5", &s1("(none + plus[7,7]) in Int"), true, false);
}

#[test]
fn group_b_cardinality_merges_the_matrix_circuit() {
    // a6/f3 — the other two UNSAT-against-SAT cells, and mt-096's pinned
    // residual R2. `BooleanMatrix.cardinality` merges the matrix's `DefCond`
    // unconditionally, so `#` guards where the `sum` reader does not.
    cell("a6", &s1q("#(none + plus[n,7]) >= 0"), true, false);
    cell("f3", &s1q("#(3 - plus[n,7]) >= 0"), true, false);
}

#[test]
fn group_b_shedding_is_not_always_sat_ward() {
    // h1 — the sixth UNSAT-against-SAT cell, and the one that could have
    // reversed the mt-096 decision. Under a literally-`Int` binder the guard is
    // `val ∨ overflow`, so SHEDDING it is FALSE-ward: `some (∅ + ∅)` is false and
    // the ∀ fails. Its control is group A's h2, the same cell swapped.
    cell(
        "h1",
        &s23("all n: Int | some (plus[n,7] + none)"),
        true,
        false,
    );
}

#[test]
fn group_b_a_literal_union_under_a_quantifier_sheds() {
    // c4 — the minimal pair against group A's c1: same denotation, `7` spelled
    // as a literal instead of a fact-pinned field, opposite verdict. Ground
    // substitution is what makes the circuit constant.
    cell("c4", &s1q("(plus[n,7] + 3) in Int"), true, true);
}

#[test]
fn group_b_lone_and_one_short_circuit_before_the_guard() {
    // d1/d2: `lone` returns TRUE and `one` returns FALSE on a cells-empty matrix
    // without ever reaching `ensureDef`. d2-vs-group-A's d3 is the discriminator
    // — the same empty set, the same negation, opposite verdicts, decided only
    // by which multiplicity keyword is used.
    cell("d1", &s1q("lone (plus[n,7] & Int)"), true, true);
    cell("d2", &s1q("not one (plus[n,7] & Int)"), false, true);
}

#[test]
fn group_b_override_tests_its_right_operand_only() {
    // e2 against group A's e1: `++` runs the emptiness test on its RIGHT operand
    // alone, so a cast on the right sheds and one on the left never does.
    cell(
        "e1",
        &s1q("((plus[n,7] -> 3) ++ (Q.h)) in (Int -> Int)"),
        true,
        false,
    );
    cell(
        "e2",
        &s1q("((Q.h) ++ (plus[n,7] -> 3)) in (Int -> Int)"),
        true,
        true,
    );
}

#[test]
fn group_b_some_sheds_on_a_constant_true_cell() {
    // f1/i9: `3 - plus[n,7]` MERGES the flag (difference) and keeps cell `3`
    // constant-TRUE, so the matrix is guarded and non-empty. `some` returns TRUE
    // the moment it sees that cell — the one shape where only the reader moves
    // (group A's f2/f4/f5 are the same set under `in`/`lone`/`no`). i9 shows the
    // reader shed applies on top of a union that KEPT the flag.
    cell("f1", &s1q("some (3 - plus[n,7])"), true, true);
    cell("i9", &s23q("some (none + (3 - plus[n,7]))"), true, true);
}

#[test]
fn group_b_chained_unions_are_binary_and_left_associative() {
    // g2/g4/j2: appending `+ 3` to a jar-UNSAT formula makes it SAT, because the
    // inner union folds to a NON-empty `{3}` and then the outer one drops the
    // empty operand. An n-ary `or` (which merges everything) would make g2 and
    // j2 UNSAT, so these also re-prove the binary left-association.
    cell("g2", &s1q("(plus[n,7] + plus[n,1] + 3) in Int"), true, true);
    cell(
        "g4",
        &s1q("((plus[n,7] + plus[n,7]) + none) in Int"),
        true,
        true,
    );
    cell(
        "j2",
        &s23q("(3 + plus[n,7] + plus[n,7]) in Int"),
        true,
        true,
    );
}

#[test]
fn group_b_partial_overflow_sheds_per_binding() {
    // i3: only the `n=7` binding overflows, so only that binding sheds — the
    // fold is per-binding, not per-node. Its control is group A's i4, the same
    // arithmetic with no union to shed through.
    let src = s23(&format!(
        "all n: {{x: Int | x>=0 and x<=7}} | {}",
        "(plus[n,1] + 3) in Int"
    ));
    cell("i3", &src, true, true);
}

#[test]
fn group_b_a_former_above_a_shedding_union_cannot_restore_it() {
    // i5 against group A's i6: once the union has dropped the circuit, the
    // intersection above it has nothing left to merge.
    cell("i5", &s23q("((plus[n,7] + none) & Int) in Int"), true, true);
}

#[test]
fn group_b_nested_unions_re_drop_the_flag() {
    // k2/k3/k4: a union above a union drops again whatever the first one kept.
    // k3 is the sharp one — the inner union KEEPS the cast's circuit, and the
    // outer union then discards the whole (still cells-empty) matrix.
    cell("k2", &s23q("((plus[n,7] + none) + 3) in Int"), true, true);
    cell("k3", &s23q("((none + plus[n,7]) + 3) in Int"), true, true);
    cell("k4", &s23q("(3 + (none + plus[n,7])) in Int"), true, true);
}

#[test]
fn group_b_the_trigger_is_the_overflow_circuit_not_plus() {
    // k5: `div[n,0]` sets the same constantly-TRUE circuit through `divByZero`,
    // and sheds through a union exactly as `plus` does. Group A's k6/k7 are the
    // controls that keep it honest.
    cell("k5", &s23q("(div[n,0] + 3) in Int"), true, true);
}

#[test]
fn group_b_emptiness_is_translation_time_not_instance_time() {
    // k8/k9 — the cells that pin the classifier as a TRANSLATION-time predicate.
    // `Node` has variable cells, so it counts as non-empty even in k9, where the
    // conjoined `no Node` empties it in every instance. A folder that consulted
    // the runtime value would answer differently in the evaluator than in the
    // encoder, and the two would stop being a matched pair.
    cell("k8", &s23q("(plus[n,7] + Node) in univ"), true, true);
    let forced = s23("(all n: {x: Int | x>=1 and x<=7} | (plus[n,7] + Node) in univ) and no Node");
    cell("k9", &forced, true, true);
}
