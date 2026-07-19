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
    let scoped = compute_universe(&world, &graph, &world.commands[idx]).expect("universe");
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
    let scoped = compute_universe(&world, &graph, &world.commands[idx]).expect("universe");
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

// ======= higher-order quantifier skolemization (mt-038, §10.6) =======

/// Whether command 0 of `src` defers at lowering (a typed `TranslateError`,
/// never a wrong verdict — STYLE E5).
fn lower_defers(src: &str) -> bool {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).is_err()
}

/// A **top-level existential** whose bound is higher-order — a mult-marked arrow
/// (`some r: A one -> one B`, `some tree: N lone -> N`) or a `set`-marked unary —
/// now **skolemizes** into a free relation instead of deferring (translation-ref
/// §10.6, probes T9a/T9b). This was the gap the mt-035 ordering models exposed
/// (ringlead/firewire). Jar-verified via the `DumpK2` probe harness: each of these
/// solves (SAT) rather than raising `HigherOrderDeclException`.
#[test]
fn higher_order_existential_skolemizes_sat() {
    // jar: SAT — some 2-atom relation `r ⊆ A×B` that is injective + total-ish and
    // non-empty exists at scope 3.
    assert_sat("sig A {}\nsig B {}\nrun { some r: A one -> one B | some r } for 3\n");
    // jar: SAT — a partial-function successor tree over N.
    assert_sat("sig N {}\nrun { some tree: N lone -> N | N in N.tree } for 3\n");
    // jar: SAT — `some r: set A | some r` (a non-empty subset of A exists).
    assert_sat("sig A {}\nrun foo { some r: set A | some r } for 3\n");
    // A plain product bound is first-order (a single pair) — no skolem, still SAT.
    assert_sat("sig A {}\nsig B {}\nrun { some r: A -> B | some r } for 2\n");
    // A first-order sig quantifier is unaffected — still SAT.
    assert_sat("sig A {}\nrun { some x: A | x = x } for 2\n");
}

/// A higher-order decl at **universal** polarity, or nested under a universal,
/// cannot be skolemized at depth 0 — the jar raises `HigherOrderDeclException`
/// ("Analysis cannot be performed since it requires higher-order quantification
/// that could not be skolemized"). mettle defers with the same typed error
/// (`TranslateError::HigherOrder`), never a wrong verdict (probes T9d/T9e,
/// jar-verified).
#[test]
fn higher_order_universal_defers_typed() {
    // `all r: set A | …` — effective-universal, not skolemizable (jar: ERROR).
    assert!(lower_defers(
        "sig A {}\nrun foo { all r: set A | some r } for 3\n"
    ));
    // A HO existential nested under a universal `all x: A` (jar: ERROR).
    assert!(lower_defers(
        "sig A {}\nrun foo { all x: A | some r: set A | x in r } for 3\n"
    ));
}

/// A `check` negates the assertion, so a **universal** higher-order decl in the
/// assertion body becomes an effective existential after NNF and **is**
/// skolemizable (translation-ref §10.6, probe T9c). `all f: A lone -> B | some f`
/// asserts every injective partial map A→B is non-empty; the empty map is a
/// counterexample, so the `check` is SAT (a counterexample found) in the jar.
#[test]
fn higher_order_check_negation_skolemizes_sat() {
    // jar: SAT (counterexample = the empty relation, which is `lone` per column
    // yet not `some`).
    assert_sat("sig A {}\nsig B {}\nassert Inj { all f: A lone -> B | some f }\ncheck Inj for 3\n");
}

/// A run-pred **relation-valued parameter** binds as a free skolem relation
/// (translation-ref §10.6, probe T9f): `pred p[r: A -> B] { some r } run p` is
/// SAT (some non-empty A→B relation exists). A `set`-marked unary param likewise.
#[test]
fn run_pred_relational_param_skolemizes_sat() {
    // jar: SAT.
    assert_sat("sig A {}\nsig B {}\npred p[r: A -> B] { some r }\nrun p for 3\n");
    // jar: SAT — a `set`-marked unary param.
    assert_sat("sig A {}\npred q[s: set A] { some s }\nrun q for 3\n");
    // A plain unary param (default `one`) stays first-order — still SAT.
    assert_sat("sig A {}\npred u[x: A] { x = x }\nrun u for 2\n");
}

/// A skolem's membership constraint is real: `some r: some A | some r` demands a
/// non-empty subset of `A`, but the fact `no A` empties `A`, so no witness exists
/// — jar UNSAT. Confirms the skolem is bounded/constrained by its decl, not free
/// to roam the whole universe (translation-ref §10.6).
#[test]
fn higher_order_skolem_membership_unsat() {
    // jar: UNSAT.
    assert_unsat("sig A {}\nfact { no A }\nrun { some r: some A | some r } for 3\n");
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

/// A post-colon `disj` on a **field** (`f: disj e`) is jar-pinned and lowered
/// (mt-040) — see `field_bound_disj_*` below. A post-colon `disj` on a
/// **quantifier / run-pred param** decl (`x: disj e`) is a jar **resolve error**
/// ("Local variable ... cannot be bound to a 'disjoint' expression", jar-probed
/// 2026-07-18): mettle accepts it leniently at resolve (mt-027 over-accept
/// class) and must **defer typed** at lowering, never silently drop the
/// constraint. Zero corpus incidence; this pins that negative space.
#[test]
fn post_colon_disj_quant_decl_defers_typed() {
    // Quantifier decl bound — the jar rejects this at resolve; mettle defers.
    assert!(lower_defers(
        "sig E {}\nrun { all x, y: disj E | x = y } for 3\n"
    ));
}

/// A post-colon `disj` field bound (`f: disj e`) adds cross-atom value
/// disjointness (mt-040): for distinct owner atoms `this != that`,
/// `no (this.f & that.f)`. Jar-pinned via `DumpK2` (the exact Kodkod formula)
/// and decisive SAT/UNSAT probes (jar 6.2.0, sym 0, noOverflow true,
/// 2026-07-18).
#[test]
fn field_bound_disj_lowers() {
    // Distinct owners sharing a value is forbidden ⟹ UNSAT (jar UNSAT).
    assert_unsat(
        "sig B {}\nsig A { f: disj set B }\n\
         run { some a1, a2: A | a1 != a2 and some (a1.f & a2.f) } for 4\n",
    );
    // The same model without `disj` allows the overlap ⟹ SAT (jar SAT) —
    // proves the disjointness fact is what forbids it, not some other constraint.
    assert_sat(
        "sig B {}\nsig A { f: set B }\n\
         run { some a1, a2: A | a1 != a2 and some (a1.f & a2.f) } for 4\n",
    );
    // A disj field is otherwise satisfiable (jar SAT).
    assert_sat("sig B {}\nsig A { f: disj set B }\nrun { some A } for 3\n");
}

/// A multiplicity-marked arrow on the right of `in` constrains the columns,
/// exactly like a field decl of that shape (`isIn`; the hotel2.als
/// `Room<:keys in Room lone-> Key` fact). Silently stripping the marks
/// lowered it to a plain product and produced the mt-037 wrong verdict:
/// mettle=SAT (a key in two rooms) vs jar=UNSAT. Both goldens jar-verified
/// 2026-07-18.
#[test]
fn in_mult_arrow_rhs_enforces_columns() {
    // `lone ->`: each Key in at most one Room ⇒ a shared key is UNSAT.
    assert_unsat(
        "sig Key {}\nsig Room { keys: set Key }\n\
         fact { Room<:keys in Room lone-> Key }\n\
         run { some k: Key | #(keys.k) > 1 } for 2 Room, 2 Key\n",
    );
    // Control: without the fact the same goal is SAT.
    assert_sat(
        "sig Key {}\nsig Room { keys: set Key }\n\
         run { some k: Key | #(keys.k) > 1 } for 2 Room, 2 Key\n",
    );
}

/// A multiplicity-marked arrow anywhere except a decl bound or an `in`
/// right-hand side (e.g. an `=` side) has no faithful plain-relation value;
/// it must defer typed, never silently strip to a product (STYLE E5).
#[test]
fn mult_arrow_outside_in_rhs_defers_typed() {
    assert!(lower_defers(
        "sig A {}\nsig B {}\nrun { some r: A -> B | r = A lone-> B } for 2\n"
    ));
}

/// `util/ordering`'s `min`/`max` funs, pinned against the jar (all three
/// verdicts jar-verified 2026-07-18). The clean-room stdlib originally shipped
/// the two bodies swapped (`min` returned the maximum) — caught by the mt-037
/// solve gauge as the hotel1.als[0] wrong verdict: `nextKey`'s `min` walked
/// the ordering backwards, excluding the book's counterexample.
#[test]
fn ordering_min_max_pinned() {
    let opening = "open util/ordering[A]\nsig A {}\n";
    assert_unsat(&format!(
        "{opening}run {{ min[A] != first }} for exactly 3 A\n"
    ));
    assert_unsat(&format!(
        "{opening}run {{ max[A] != last }} for exactly 3 A\n"
    ));
    assert_sat(&format!(
        "{opening}run {{ min[A] = first and max[A] = last and min[A] != max[A] }} for exactly 3 A\n"
    ));
}

// ---------------------------------------------------------------------------
// mt-040 (a): 0-param relation-valued macro used as a join base
// ---------------------------------------------------------------------------
// A top-level `let adjacent = <relation>` (0 params) invoked as a spine base
// (`n.adjacent`, `adjacent[n]` = `n.adjacent`) records nothing at the checker's
// `infer_zero_macro` type path, so the lowerer used to defer ("name without a
// recorded resolution"). The checker now carries the macro id on the winning
// base reading and `flush_rec` records a `NameChoice::Macro`, so the lowerer
// replays the macro body.  jar-verified 2026-07-18 (sym 0, noOverflow true).
#[test]
fn macro_valued_join_base_lowers() {
    // `n.adjacent` = `n.rel`; every node has a successor ⟹ SAT for 3
    // (jar: SAT count 3).
    assert_sat(
        "sig Node { rel: set Node }\nlet adjacent = rel\n\
         pred p { all n: Node | some n.adjacent }\nrun p for 3\n",
    );
}

// ---------------------------------------------------------------------------
// mt-040 (b): callable passed to a higher-order macro by bare name
// ---------------------------------------------------------------------------
// `let m[axiom] { axiom[args] }` invoked `m[pred_name]`: the checker resolves
// the body accept-lean (verdict-neutral) but now records which func/pred each
// callable-by-name argument names (`MacroChoice::callables`); the lowerer binds
// the parameter and inlines the real call.  Both verdicts jar-verified
// 2026-07-18 (sym 0, noOverflow true).
#[test]
fn higher_order_macro_callable_by_name_lowers() {
    // `checkIt[isEmpty]` ⟹ `isEmpty[S]` = `no S`; S may be empty ⟹ SAT count 1.
    assert_sat(
        "sig S {}\npred isEmpty[x: set S] { no x }\n\
         let checkIt[axiom] { axiom[S] }\nrun { checkIt[isEmpty] } for 3\n",
    );
    // `assertIt[nonEmpty]` ⟹ `nonEmpty[none]` = `some none` = false ⟹ UNSAT.
    // Discriminates a correct inline from treating `axiom` as a relation.
    assert_unsat(
        "sig S {}\npred nonEmpty[x: set S] { some x }\n\
         let assertIt[axiom] { axiom[none] }\nrun { assertIt[nonEmpty] } for 3\n",
    );
}

// ======================= enumeration conflict budget =======================
// mt-046 unlocked corpus models (e.g. `correctChord.als`) that pass the
// primary-var cap but whose per-instance solves are individually expensive, so
// a full SB-0 count can grind for hours. `SolveOptions::enum_conflict_budget`
// bounds the *cumulative* conflict spend of a whole enumeration and ends in a
// typed `exhausted()` rather than either hanging or silently truncating the
// count (see the `InstanceEnumerator` docs).

/// `sig A {}; run { some A } for 3` has exactly 7 raw instances (see
/// `count_some_a_is_seven`). A zero cumulative-conflict budget must still yield
/// at least the models found before the first real conflict (this goal's
/// non-conflicting instances), stop short of the full 7, and report
/// `exhausted()` — never a fabricated full count.
#[test]
fn enum_conflict_budget_zero_exhausts_short_of_full_count() {
    let src = "sig A {}\nrun { some A } for 3\n";
    let (ir, scoped, goal, bounds) = enum_pipeline(src, 0);
    let opts = SolveOptions {
        enum_conflict_budget: Some(0),
        ..SolveOptions::default()
    };
    let mut it = enumerate(&ir, &scoped, &goal, &bounds, &opts).expect("enumerate");
    let n = it.by_ref().count();
    assert!(
        n < 7,
        "a zero conflict budget must not reach the full 7-instance count, got {n}"
    );
    assert!(
        it.exhausted(),
        "a zero conflict budget must report exhaustion, not a quiet stop"
    );
}

/// The same goal, unbudgeted (`enum_conflict_budget: None`, the default): the
/// full exact count is reached and `exhausted()` is false — confirming the
/// budget change leaves the unbudgeted path (every existing caller) untouched.
#[test]
fn enum_conflict_budget_none_reaches_full_count_not_exhausted() {
    let src = "sig A {}\nrun { some A } for 3\n";
    let (ir, scoped, goal, bounds) = enum_pipeline(src, 0);
    let opts = SolveOptions::default();
    assert_eq!(opts.enum_conflict_budget, None);
    let mut it = enumerate(&ir, &scoped, &goal, &bounds, &opts).expect("enumerate");
    let n = it.by_ref().count();
    assert_eq!(
        n, 7,
        "unbudgeted enumeration must still reach the exact count"
    );
    assert!(
        !it.exhausted(),
        "an unbudgeted enumeration that finished must not report exhaustion"
    );
}

/// Shared pipeline setup for the budget tests (mirrors [`count`]/[`run`] but
/// returns the pieces `enumerate` needs directly, since these tests build
/// `SolveOptions` themselves rather than taking the default).
fn enum_pipeline(
    src: &str,
    idx: usize,
) -> (Ir, ScopedUniverse, als_core::LoweredGoal, BoundsResult) {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[idx]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx).expect("lower");
    (ir, scoped, goal, bounds)
}
