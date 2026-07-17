//! End-to-end solve goldens (mt-033, translation-ref §4): resolve → universe →
//! bounds → lower → encode → solve, asserting mettle's **verdict** and (for the
//! counting net) its **SB-0 enumeration count** against the reference Alloy
//! 6.2.0 jar. The jar answers are pinned in comments (symmetry 0, noOverflow
//! true = LEDGER-001 forbid, sat4j); the tests never run the jar (STYLE U3).
//!
//! Per ADR-0002 instance *tuples* are never diffed against the jar — only the
//! verdict and the SB-0 count. Every SAT verdict additionally has its decoded
//! instance checked to respect the relation bounds (`lower ⊆ decoded ⊆ upper`),
//! the property net the evaluator self-check (mt-034) later strengthens.

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, enumerate, lower_command, solve_goal, BoundsResult, Instance,
    ScopedUniverse, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Runs the whole pipeline for command `idx` of `src` and returns the verdict
/// plus the pieces needed to check bounds-respect.
fn run(src: &str, idx: usize) -> (SolveVerdict, Ir, ScopedUniverse, BoundsResult) {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &world.commands[idx]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx).expect("lower");
    let verdict =
        solve_goal(&ir, &scoped, &goal, &bounds, &SolveOptions::default()).expect("solve");
    (verdict, ir, scoped, bounds)
}

/// Asserts the command's verdict is SAT, and the instance respects the bounds.
fn assert_sat(src: &str) {
    let (verdict, _ir, _scoped, bounds) = run(src, 0);
    match verdict {
        SolveVerdict::Sat(inst) => assert_bounds_respected(&inst, &bounds),
        SolveVerdict::Unsat => panic!("expected SAT (jar-verified), got UNSAT:\n{src}"),
        // No budget set (default options), so `Unknown` is unreachable.
        SolveVerdict::Unknown => unreachable!("unbudgeted solve returned Unknown"),
    }
}

/// Asserts the command's verdict is UNSAT.
fn assert_unsat(src: &str) {
    let (verdict, _ir, _scoped, _bounds) = run(src, 0);
    assert!(
        matches!(verdict, SolveVerdict::Unsat),
        "expected UNSAT (jar-verified), got SAT:\n{src}"
    );
}

/// Property net (ADR-0011 item 5 / §6): every decoded relation lies between its
/// lower and upper bound.
fn assert_bounds_respected(inst: &Instance, bounds: &BoundsResult) {
    for (rel, bound) in bounds.bounds.iter() {
        let decoded = inst.get(rel).expect("every bounded relation is decoded");
        assert!(
            bound.lower().is_subset_of(decoded),
            "lower ⊄ decoded for {rel:?}"
        );
        assert!(
            decoded.is_subset_of(bound.upper()),
            "decoded ⊄ upper for {rel:?}"
        );
    }
}

/// Exhaustively enumerates command `idx` of `src` and returns the SB-0 count.
fn count(src: &str, idx: usize) -> usize {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &world.commands[idx]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx).expect("lower");
    enumerate(&ir, &scoped, &goal, &bounds, &SolveOptions::default())
        .expect("enumerate")
        .count()
}

// ============================ verdict goldens ============================
// Each model was run through OracleShim (symmetry 0, noOverflow true, sat4j).

/// Quantifier over a join (a node in its own successors). Jar: SAT.
#[test]
fn quantifier_over_join_sat() {
    assert_sat("sig Node { next: set Node }\nrun { some n: Node | n in n.next } for 3\n");
}

/// A total successor function on a non-empty finite domain must cycle, so
/// acyclicity is unsatisfiable. Jar: UNSAT.
#[test]
fn acyclicity_unsat() {
    assert_unsat(
        "sig N { nx: one N }\nfact acyclic { no n: N | n in n.^nx }\nrun { some N } for 3\n",
    );
}

/// Two `in` subset sigs, disjoint and both inhabited. Jar: SAT.
#[test]
fn subset_in_sigs_sat() {
    assert_sat(
        "sig A {}\nsig B in A {}\nsig C in A {}\nrun { some B and some C and no (B & C) } for 3\n",
    );
}

/// REGRESSION (latent mt-031 resolver bug, surfaced by the corpus solve sweep
/// on `examples/systems/javatypes_soundness.als`): a sig field used as a
/// **box-join base** inside its own sig fact, where the join arg does *not* fill
/// the field's owner column (`holds[S]` for a `State`/`Obj` field
/// `holds: S -> lone V`), must keep its implicit `this` (`this.holds`) so the arg
/// joins the field's declared domain — arity 1 — not the raw owner-headed
/// relation (arity 2). The old resolver stripped implicit `this` from *every*
/// join base, so `holds[S] & V` intersected an arity-2 with an arity-1 and the
/// encoder panicked (`intersect arity mismatch`). Jar accepts the model; this
/// minimal shape is SAT (some `Obj` maps a slot to a value). The full model's
/// command [0] is UNSAT per the corpus baseline (`check TypeSoundness for 3`).
#[test]
fn sig_field_boxjoin_keeps_implicit_this_sat() {
    assert_sat(
        "sig V {}\nsig S {}\nsig Obj { holds: S -> lone V } { some holds[S] & V }\nrun {} for 3\n",
    );
}

/// Two `extends` children of an abstract parent, explicitly scoped. Jar: SAT.
#[test]
fn extends_children_sat() {
    assert_sat(
        "abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun { some B and some C } for 3 but exactly 1 B, exactly 1 C\n",
    );
}

/// REGRESSION (mt-029 scope bug, found by mt-033's baseline diff, fixed at
/// review): an abstract parent whose two `extends` children are *unscoped*
/// under a default `for 3`. The reference's derivation rules run as **full
/// passes** (both children inherit the parent scope in one
/// `derive_scope_from_parent` sweep, probe S1), so each child gets ≤ 3; the
/// old per-change-restart fixpoint let the abstract-difference rule fire on a
/// half-updated state and back-derive `C = A(3) − B(3) = 0`, making `some C`
/// wrongly UNSAT. Jar: SAT (`#C = 2` also SAT).
#[test]
fn abstract_unscoped_children_scope_bug() {
    assert_sat(
        "abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun { some B and some C } for 3\n",
    );
}

/// A `one` field multiplicity. Jar: SAT.
#[test]
fn field_one_multiplicity_sat() {
    assert_sat("sig B {}\nsig A { f: one B }\nrun { some A } for 2\n");
}

/// Cardinality equality within scope. Jar: SAT.
#[test]
fn cardinality_eq_sat() {
    assert_sat("sig A {}\nrun { #A = 2 } for 3\n");
}

/// Cardinality above the scope is unsatisfiable. Jar: UNSAT.
#[test]
fn cardinality_gt_unsat() {
    assert_unsat("sig A {}\nrun { #A > 3 } for 3\n");
}

/// `check` polarity: the assertion `some A` has a counterexample (empty A),
/// so the check is SAT (a counterexample was found). Jar: SAT.
#[test]
fn check_polarity_counterexample() {
    assert_sat("sig A {}\nassert SomeA { some A }\ncheck SomeA for 3\n");
}

/// A `one` sig's field (denoted `owner -> stored`). Jar: SAT.
#[test]
fn one_sig_field_sat() {
    assert_sat("sig A {}\none sig Cfg { limit: one A }\nrun { some Cfg.limit } for 3\n");
}

/// An abstract parent equal to the union of its `one` children. Jar: SAT.
#[test]
fn abstract_children_union_sat() {
    assert_sat(
        "abstract sig A {}\none sig X extends A {}\none sig Y extends A {}\nrun { A = X + Y } for 3\n",
    );
}

/// Reflexive-transitive closure reachability. Jar: SAT.
#[test]
fn reflexive_closure_sat() {
    assert_sat("sig N { nx: set N }\nrun { some n: N | N in n.*nx } for 3\n");
}

/// A `lone` sig forced empty. Jar: SAT.
#[test]
fn lone_sig_empty_sat() {
    assert_sat("lone sig A {}\nsig B {}\nrun { no A } for 3\n");
}

/// Transpose in a join. Jar: SAT.
#[test]
fn transpose_sat() {
    assert_sat("sig N { r: set N }\nrun { some n: N | some (n.~r) } for 3\n");
}

/// An `Int`-valued field compared to a literal (`Int[·]`/`int[·]` slice). Jar: SAT.
#[test]
fn int_field_compare_sat() {
    assert_sat("sig A { n: one Int }\nrun { some a: A | a.n = 1 } for 3\n");
}

/// Two cardinalities compared (both-int `IntCompare`). Jar: SAT.
#[test]
fn cardinality_compare_sat() {
    assert_sat("sig A {}\nsig B {}\nrun { #A = #B and some A } for 3\n");
}

/// Relational override over a nested field. Jar: SAT.
#[test]
fn override_sat() {
    assert_sat("sig K {}\nsig V {}\nsig M { m: K -> lone V }\nrun { some x: M | some (x.m ++ x.m) } for 3\n");
}

// ========================= SB-0 enumeration counts =========================

/// translation-ref probe T3: `run { some A } for 3` has **7** raw (SB-0)
/// instances (the non-empty subsets of a 3-atom set). Jar: 7.
#[test]
fn count_some_a_is_seven() {
    assert_eq!(count("sig A {}\nrun { some A } for 3\n", 0), 7);
}

/// `#A = 2` at scope 3 has **3** raw instances (the 2-subsets of 3 atoms).
/// Jar: 3.
#[test]
fn count_card_two_is_three() {
    assert_eq!(count("sig A {}\nrun { #A = 2 } for 3\n", 0), 3);
}

/// The marquee number: `oracle/test1.als`'s `show` (`run { some r } for 3`)
/// enumerates **1129** raw (SB-0) instances. Jar: 1129.
#[test]
fn count_test1_show_is_1129() {
    let src = "sig A {}\nsig B {\n\tr: set A\n}\npred show {\n\tsome r\n}\nrun show for 3\n";
    assert_eq!(count(src, 0), 1129);
}

/// `oracle/test1.als`'s `check NoEmpty` (`all b: B | some b.r`, negated to
/// `some b: B | no b.r`) is **SAT** — a counterexample exists. The jar's SB-0
/// count is **561**, but mettle's is **464**: this is the documented
/// **skolemization divergence** (translation-ref §2.3, ADR-0011 — mettle does
/// not skolemize). The jar's `skolemDepth 0` turns the top-level existential
/// into a skolem constant relation `$NoEmpty_b`, whose assignments are counted
/// too, multiplying the raw count by the number of witnesses per instance. This
/// never changes the verdict, only the count — so SB-0 count parity holds only
/// for goals without a skolemizable top-level existential (e.g. `some r` above,
/// which matches at 1129). We assert the verdict and pin mettle's own count.
#[test]
fn check_test1_sat_skolem_count_divergence() {
    let src = "sig A {}\nsig B {\n\tr: set A\n}\nassert NoEmpty {\n\tall b: B | some b.r\n}\ncheck NoEmpty for 3\n";
    let (verdict, ..) = run(src, 0);
    assert!(
        matches!(verdict, SolveVerdict::Sat(_)),
        "counterexample exists"
    );
    // mettle's own (un-skolemized) SB-0 count is stable at 464; the jar's is 561.
    assert_eq!(count(src, 0), 464);
}

// ===================== known limitation (mt-037 owns) =====================

/// KNOWN GAP (root-caused by mt-034, fix owned by mt-037): a field-group `disj`
/// is dropped. `disj a, b: set E` declares `a`/`b` pairwise disjoint, so
/// `all s: S | no (s.a & s.b)` is a **theorem** — jar UNSAT (no counterexample).
/// mettle's `als_types::ResolvedField` does not record the `disj` marker (the
/// `Decl` AST carries `is_disj`), so the lowerer never synthesizes the
/// disjointness and mettle finds a **spurious counterexample → SAT**. This is
/// the sole cause of the `mediaAssets.als[3]` (`check PasteNotAffectHidden`)
/// baseline disagreement (translation-ref §10.5). The self-check *passes* on the
/// instance (mettle's goal is genuinely satisfied — it is just too weak), so this
/// is a lowering/synthesized-fact gap, not an encoder bug. When mt-037 records
/// field-`disj` and synthesizes it, this flips to UNSAT — update the assertion
/// then.
#[test]
fn field_disj_dropped_known_gap() {
    // jar: UNSAT (theorem). mettle (current, wrong): SAT.
    assert_sat("sig E {}\nsig S { disj a, b: set E }\nassert D { all s: S | no (s.a & s.b) }\ncheck D for 3\n");
    // Control: without `disj` the assertion is genuinely violable — SAT in both.
    assert_sat(
        "sig E {}\nsig S { a, b: set E }\nassert D { all s: S | no (s.a & s.b) }\ncheck D for 3\n",
    );
}

// ============================== determinism ==============================

/// D1/U4: two independent solves of the same command give the same verdict and
/// the same SB-0 count.
#[test]
fn determinism_two_runs_identical() {
    let src = "sig A {}\nsig B {\n\tr: set A\n}\nrun { some r } for 3\n";
    assert_eq!(count(src, 0), count(src, 0));
    let a = matches!(run(src, 0).0, SolveVerdict::Sat(_));
    let b = matches!(run(src, 0).0, SolveVerdict::Sat(_));
    assert_eq!(a, b);
}
