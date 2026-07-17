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

// ================= util/ordering exact bounds (LEDGER-004) =================
// The approved two-part rule, tested as two DISTINCT behaviors at symmetry 0
// (mettle's regime — ADR-0002). Every count is jar-verified via OracleShim
// (`--symmetry 0 --enumerate exhaustive`, noOverflow forbid); the tests never
// run the jar (STYLE U3).
//
// (a) PINNING ENGAGES — the ordered sig has no partition choice (a childless
//     leaf, or an enum): `first`/`last`/`next` are bound to exact constants over
//     the atoms in universe order, so the linear order is fully determined and
//     exactly ONE instance survives at sym0 (probes T4/T4b/T10/T12/T13/T19).
// (b) PINNING DOES NOT ENGAGE — a proper subsig leaves genuine order freedom:
//     `first`/`next` are governed only by the hand-built `pred/totalOrder`
//     formula, so multiple instances survive, the raw sym0 count being
//     (partition choices) × (n! linear orders) (probes T14a/b/c/e, T15).

/// (a) A childless ordered sig is pinned to a single linear order — exactly ONE
/// instance at sym0, for every size N=2..6 (probes T10a-e/T4b, jar sym0 = 1).
/// The order is `S$0 -> S$1 -> … -> S$<N-1>`; uniqueness comes from the exact
/// bounds on `first`/`next`, not symmetry breaking (mettle does none).
#[test]
fn ledger004_childless_ordered_sig_pins_single_instance() {
    for n in 2..=6 {
        let src = format!("open util/ordering[A]\nsig A {{}}\nrun {{}} for {n} A\n");
        assert_eq!(
            count(src.as_str(), 0),
            1,
            "childless ordered sig, for {n} A"
        );
    }
}

/// (a) Merely *opening* the module pins the order even when `first`/`next`/
/// `last` are never referenced by the command: `run { some A }` has ONE
/// instance with the open, and **7** without it (probe T19, jar sym0 = 1 vs 7).
#[test]
fn ledger004_open_alone_pins_single_instance() {
    assert_eq!(
        count("open util/ordering[A]\nsig A {}\nrun { some A }\n", 0),
        1
    );
    // Control: no `open` → the 7 non-empty subsets of a 3-atom set (probe T3).
    assert_eq!(count("sig A {}\nrun { some A } for 3\n", 0), 7);
}

/// (a) An `enum` auto-opens ordering with the same single-instance pinning —
/// `first` = the first declared constant, chain in declaration order (probe
/// T13, jar sym0 = 1).
#[test]
fn ledger004_enum_pins_single_instance() {
    assert_eq!(count("enum Color { Red, Blue, Green }\nrun {}\n", 0), 1);
}

/// (a) Two independent `open util/ordering` on distinct sigs pin independently —
/// still ONE combined instance (probe T12, jar sym0 = 1).
#[test]
fn ledger004_two_independent_opens_pin() {
    let src = "open util/ordering[A] as oa\nopen util/ordering[B] as ob\n\
               sig A {}\nsig B {}\nrun {} for 3 A, 4 B\n";
    assert_eq!(count(src, 0), 1);
}

/// (a) The pin is a genuine hard constant, not a solver preference: a fact
/// asserting `first & last` is non-empty is UNSAT over 3 pinned atoms (first =
/// S$0, last = S$2, disjoint) yet SAT over 1 (first = last), proving no
/// alternate atom can be chosen to dodge the fact (probe T16, jar UNSAT). Also
/// exercises the inlined `first`/`last` funcs (`last = elem - next.elem`).
#[test]
fn ledger004_pin_is_hard_constant() {
    assert_unsat(
        "open util/ordering[S] as ord\nsig S {}\n\
                  fact { some (ord/first & ord/last) }\nrun {} for 3 S\n",
    );
    assert_sat(
        "open util/ordering[S] as ord\nsig S {}\n\
                fact { some (ord/first & ord/last) }\nrun {} for 1 S\n",
    );
}

/// (b) A non-abstract ordered sig with a proper (inexact) subsig leaves genuine
/// order freedom — pinning does NOT engage, the `pred/totalOrder` formula
/// governs `first`/`next`, and the raw sym0 count is (subset choices for B) ×
/// (3! orders) = 7 × 6 = **42** for `for 3 A, 2 B` (probe T14a, jar sym0 = 42).
#[test]
fn ledger004_subsig_partition_no_pin_count_42() {
    let src = "open util/ordering[A]\nsig A {}\nsig B extends A {}\nrun {} for 3 A, 2 B\n";
    assert_eq!(count(src, 0), 42);
}

/// (b) Rank freedom isolated from population freedom: with the subsig forced to
/// exactly one atom, the instances share the identical atom population but seat
/// B at a different chain rank — sym0 count **6** = 3 ranks × 2! (probe T14b,
/// jar sym0 = 6).
#[test]
fn ledger004_subsig_rank_freedom_count_6() {
    let src = "open util/ordering[A]\nsig A {}\nsig B extends A {}\nrun {} for 3 A, exactly 1 B\n";
    assert_eq!(count(src, 0), 6);
}

/// (b) Two children under an abstract ordered parent, each `exactly`-scoped,
/// still leave rank-tagging freedom — sym0 count **6** (probe T14c, jar-verified
/// sym0 = 6 on 2026-07-17; the matrix's earlier `3` was the sym20 value).
#[test]
fn ledger004_abstract_two_exact_children_count_6() {
    let src = "open util/ordering[A]\nabstract sig A {}\nsig B, C extends A {}\n\
               run {} for 3 A, exactly 2 B, exactly 1 C\n";
    assert_eq!(count(src, 0), 6);
}

/// (b) The degenerate collapse (`exactly 3 B` under `3 A`, so B ≡ A): the jar's
/// count-1 for this case is a **symmetry-breaking** effect (sym20 only). At
/// sym0 the exact-constant pinning does NOT re-engage and the raw count is
/// 3! = **6** (jar-verified sym0 = 6 on 2026-07-17). mettle, a sym0 engine,
/// must not pin here — its eligibility rule (childless-or-enum) correctly does
/// not, matching the jar's raw count.
#[test]
fn ledger004_subsig_full_collapse_no_pin_at_sym0_count_6() {
    let src = "open util/ordering[A]\nsig A {}\nsig B extends A {}\nrun {} for 3 A, exactly 3 B\n";
    assert_eq!(count(src, 0), 6);
}

/// (b-control) A field reference to the ordered sig from an *unrelated* sig does
/// NOT disturb its pinning — only a subsig partition does (probe T15). `sig T {
/// f: S }` over `for 3 S, 2 T` keeps S's order pinned and the count is entirely
/// T's field freedom: sym0 = **16** (jar sym0 = 16).
#[test]
fn ledger004_unrelated_field_still_pins_count_16() {
    let src = "open util/ordering[S]\nsig S {}\nsig T { f: S }\nrun {} for 3 S, 2 T\n";
    assert_eq!(count(src, 0), 16);
}

// ============ higher-order relation quantifier — typed defer ============

/// Whether command 0 of `src` defers at lowering (a typed `TranslateError`,
/// never a wrong verdict — STYLE E5).
fn lower_defers(src: &str) -> bool {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).is_err()
}

/// A quantifier whose bound is a **multiplicity-marked arrow** (`some r: A one
/// -> one B | …`, `some tree: Node lone -> Node | …`) ranges over sub-relations,
/// not tuples — genuinely higher-order (the jar skolemizes it; mettle does not).
/// It is a typed defer, never a per-tuple wrong verdict. This is the gap the
/// mt-035 ordering models exposed (ringlead/firewire over-/under-constrained
/// before the defer). A plain arrow bound stays first-order (one pair per
/// binding, the jar's reading), and a sig quantifier is unaffected.
#[test]
fn higher_order_arrow_quantifier_defers() {
    assert!(lower_defers(
        "sig A {}\nsig B {}\nrun { some r: A one -> one B | some r }\n"
    ));
    assert!(lower_defers(
        "sig N {}\nrun { some tree: N lone -> N | N in N.tree }\n"
    ));
    // A plain product bound is first-order (a single pair) — must NOT defer.
    assert!(!lower_defers(
        "sig A {}\nsig B {}\nrun { some r: A -> B | some r } for 2\n"
    ));
    // A first-order sig quantifier is unaffected.
    assert!(!lower_defers("sig A {}\nrun { some x: A | x = x } for 2\n"));
}

// ===================== known limitation (mt-037 owns) =====================

/// mt-038 regression pin: a field-group `disj` synthesizes the pairwise
/// disjointness fact. `disj a, b: set E` declares `a`/`b` pairwise disjoint, so
/// `all s: S | no (s.a & s.b)` is a **theorem** — jar UNSAT (no counterexample).
/// mettle now records the `disj` marker (`ResolvedSig::field_disj_groups`) and
/// the lowerer emits `no (S.a & S.b)`, so the `check` is UNSAT to match. This
/// was the sole `mediaAssets.als[3]` (`check PasteNotAffectHidden`) baseline
/// disagreement (translation-ref §10.5); previously mettle dropped the fact and
/// found a spurious counterexample (SAT).
#[test]
fn field_disj_synthesizes_disjointness() {
    // jar: UNSAT (theorem) — the disjointness makes `no (s.a & s.b)` valid.
    assert_unsat(
        "sig E {}\nsig S { disj a, b: set E }\nassert D { all s: S | no (s.a & s.b) }\ncheck D for 3\n",
    );
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
