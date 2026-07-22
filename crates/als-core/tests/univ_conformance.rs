//! `univ`/`iden` **live-universe** conformance (mt-053, LEDGER-011,
//! translation-ref §10.8). Jar-free and CI-safe: every pinned count/verdict was
//! produced by running the reference jar (`oracle/org.alloytools.alloy.dist.jar`,
//! Alloy 6.2.0, `sat4j`, `noOverflow=true`) at **probe time** on the model quoted
//! in each test — see `scratchpad/probe/mt053/NOTES.md` for the full matrix,
//! arithmetic, and per-cell reflexivity controls. The tests assert mettle's own
//! enumeration count / verdict equals the jar's, never calling the jar at test
//! time (STYLE U3).
//!
//! The change under test: `univ`/`iden` in **user-expression** position lower to
//! the jar's *live union* `Int ∪ String ∪ ⋃(top-level sig populations)`, a
//! genuinely per-instance-dynamic set — not the all-atoms constant. Int/String
//! atoms (padding included) are unconditionally present; a dead
//! (allocated-but-empty) atom of a non-exact top-level sig is excluded exactly
//! in the instances where that sig doesn't currently contain it.

use als_core::ir::Ir;
use als_core::{compute_bounds, compute_universe, enumerate, lower_command, SolveOptions};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Exhaustively enumerates command `cmd` of `src` at symmetry cap `symmetry` and
/// returns the count (`symmetry = 0` = raw SB-0 count; verdict is
/// symmetry-independent, so `count > 0` iff SAT).
fn count_cmd(src: &str, cmd: usize, symmetry: u32) -> usize {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[cmd]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, cmd).expect("lower");
    let opts = SolveOptions {
        symmetry,
        ..SolveOptions::default()
    };
    enumerate(&ir, &scoped, &goal, &bounds, &opts)
        .expect("enumerate")
        .count()
}

/// Command-0 count at symmetry `symmetry`.
fn count_at(src: &str, symmetry: u32) -> usize {
    count_cmd(src, 0, symmetry)
}

/// Whether command `cmd` of `src` is SAT (enumeration non-empty; verdict is
/// symmetry-independent so the default cap is used).
fn is_sat_cmd(src: &str, cmd: usize) -> bool {
    count_cmd(src, cmd, 20) > 0
}

/// Whether command 0 of `src` is SAT.
fn is_sat(src: &str) -> bool {
    is_sat_cmd(src, 0)
}

// ============================ row 1 — baseline ============================

/// Row 1 (the mt-053-filing divergence, now **closed**): a `univ`-typed field
/// `f: A -> univ` over a non-exact `A` counts the *live* universe, not all
/// atoms. `sig A { f: A -> univ } run { some f } for 2 A, 1 Int` = **65549** at
/// SB-0 (was mettle's divergent 65565 under all-atoms `univ`), **32902** at
/// SB=20. Probe: `mt053/row1_baseline.als`.
#[test]
fn row1_univ_field_baseline() {
    let src = "sig A { f: A -> univ }\nrun { some f } for 2 A, 1 Int\n";
    assert_eq!(count_at(src, 0), 65549, "row1 SB=0 = 65549 (live univ)");
    assert_eq!(count_at(src, 20), 32902, "row1 SB=20 = 32902");
}

// ===================== row 2 — Int unconditionally live =====================

/// Row 2a: `Int` atoms are in `univ` even when `Int` is mentioned nowhere.
/// `sig A {} run { some u: univ | u not in A } for exactly 1 A, 2 Int` = **SAT**
/// (`u` may be an int atom). Probe: `mt053/row2a_int_sat.als`.
#[test]
fn row2a_int_unconditional_sat() {
    let src = "sig A {}\nrun { some u: univ | u not in A } for exactly 1 A, 2 Int\n";
    assert!(is_sat(src), "row2a SAT (Int unconditionally in univ)");
}

/// Row 2b: Int's unconditional contribution scales with bitwidth. `A` exact-1
/// (always live), Int scope varied. `sig A { f: A -> univ } run { some f }`:
/// **31** at `for exactly 1 A, 2 Int` (|univ|=1+4, 2^5−1); **511** at
/// `3 Int` (|univ|=1+8, 2^9−1). Probes: `mt053/row2b_n2.als`, `row2b_n3.als`.
#[test]
fn row2b_int_scaling() {
    let n2 = "sig A { f: A -> univ }\nrun { some f } for exactly 1 A, 2 Int\n";
    let n3 = "sig A { f: A -> univ }\nrun { some f } for exactly 1 A, 3 Int\n";
    assert_eq!(count_at(n2, 0), 31, "row2b n=2 SB=0 = 31");
    assert_eq!(count_at(n3, 0), 511, "row2b n=3 SB=0 = 511");
}

// ================== row 3 — String (padding) unconditionally live ==================

/// Row 3a: padding `String` atoms (scope beyond the referenced literal) are in
/// `univ`, exactly like Int atoms. `sig A {} run { some u: univ | u not in A and
/// u != "x" and "x" in String } for exactly 1 A, exactly 3 String` = **SAT**
/// (a padding atom witnesses `u`). Probe: `mt053/row3a_string_padding_sat.als`.
#[test]
fn row3a_string_padding_sat() {
    let src = "sig A {}\n\
               run { some u: univ | u not in A and u != \"x\" and \"x\" in String } \
               for exactly 1 A, exactly 3 String\n";
    assert!(is_sat(src), "row3a SAT (padding String atoms in univ)");
}

/// Row 3b: padding's contribution scales with String scope. `A` exact-1, Int
/// bitwidth 1 (2 atoms). `sig A { f: A -> univ } run { some f and "x" in String
/// }`: **31** at `exactly 2 String` (|univ|=1+2+2, 2^5−1); **63** at
/// `exactly 3 String` (|univ|=1+2+3, 2^6−1). Probes: `mt053/row3b_n2.als`,
/// `row3b_n3.als`.
#[test]
fn row3b_string_scaling() {
    let n2 = "sig A { f: A -> univ }\n\
              run { some f and \"x\" in String } for exactly 1 A, 1 Int, exactly 2 String\n";
    let n3 = "sig A { f: A -> univ }\n\
              run { some f and \"x\" in String } for exactly 1 A, 1 Int, exactly 3 String\n";
    assert_eq!(count_at(n2, 0), 31, "row3b n=2 SB=0 = 31");
    assert_eq!(count_at(n3, 0), 63, "row3b n=3 SB=0 = 63");
}

// ============= rows 4/7 — dead-atom exclusion (dynamic per instance) =============

/// Rows 4 & 7 (the decisive live-vs-all-atoms cell): a dead atom of a non-exact,
/// currently-empty top-level sig is **excluded** from `univ`. `B` (scope 1,
/// forced empty by `no B`) allocates `b0` but never populates `B`, so `b0` is
/// unreachable through `univ` → **UNSAT** (all-atoms would be SAT via `u = b0`).
/// Probe: `mt053/row4_7_dead_atom_sat.als`.
#[test]
fn row4_7_dead_atom_excluded_unsat() {
    let src = "sig A {}\nsig B {}\n\
               run {\n  no B\n  some u: univ | u not in A and u not in Int and u not in String\n} \
               for exactly 1 A, 1 B\n";
    assert!(
        !is_sat(src),
        "row4/7 UNSAT (dead b0 excluded from live univ)"
    );
}

/// Rows 4/7 reflexivity control: `no B` alone does not kill satisfiability, and
/// `a0` stays reachable via `univ`. `run { no B and some u: univ | u in A }` =
/// **SAT**. Probe: `mt053/ctrl_no_B_sat.als`.
#[test]
fn row4_7_control_no_b_sat() {
    let src = "sig A {}\nsig B {}\n\
               run { no B and some u: univ | u in A } for exactly 1 A, 1 B\n";
    assert!(is_sat(src), "row4/7 control SAT");
}

// ============ row 5 — subset/extends contribute nothing extra ============

/// Row 5: declaring a subset (`in`) or `extends` child of `A` does not
/// double-count into `univ` (idempotent union). All three variants count
/// **7** at SB-0 (|univ| = 1(A) + 2(Int), 2^3−1). Probes:
/// `mt053/row5a_control.als`, `row5a_subset_count.als`, `row5b_extends_count.als`.
#[test]
fn row5_subset_extends_no_double_count() {
    let control = "sig A { f: A -> univ }\nrun { some f } for exactly 1 A, 1 Int\n";
    let subset = "sig A { f: A -> univ }\nsig B in A {}\n\
                  run { some f and no B } for exactly 1 A, 1 Int\n";
    let extends = "sig A { f: A -> univ }\nsig A1 extends A {}\n\
                   run { some f and no A1 } for exactly 1 A, 1 Int\n";
    assert_eq!(count_at(control, 0), 7, "row5a control SB=0 = 7");
    assert_eq!(
        count_at(subset, 0),
        7,
        "row5a subset SB=0 = 7 (no double-count)"
    );
    assert_eq!(
        count_at(extends, 0),
        7,
        "row5b extends SB=0 = 7 (no double-count)"
    );
}

// ============================ row 6 — `iden` ============================

/// Row 6a (control, non-discriminating): `r in iden` over a `set A` field. `r`'s
/// domain/range are already bound to `A`, so this collapses to the same count
/// under both hypotheses. `sig A { r: set A } run { r in iden } for 2 A` = **9**
/// at SB-0. Exercises `iden`'s live (binary) lowering. Probe:
/// `mt053/row6a_iden_field.als`.
#[test]
fn row6a_iden_field_control() {
    let src = "sig A { r: set A }\nrun { r in iden } for 2 A\n";
    assert_eq!(count_at(src, 0), 9, "row6a SB=0 = 9");
}

/// Row 6b (the decisive `iden` cell): `iden` is live-restricted, tracking the
/// same dynamic liveness as `univ`. With `B` (non-exact) forced empty,
/// `#(iden - (Int -> Int))` counts only the live diagonal = `|A| = 1`, so the
/// `= 2` command (`r2`) is **UNSAT** and the `= 1` command (`r1`) is **SAT**.
/// `Int -> Int` is subtracted to sidestep the int-representability trap; `3 Int`
/// makes the literals 1/2 representable. Probe: `mt053/row6b_iden_card.als`.
#[test]
fn row6b_iden_live_restricted() {
    let src = "sig A {}\nsig B {}\n\
               run r2 { no B and #(iden - (Int -> Int)) = 2 } for exactly 1 A, 1 B, 3 Int\n\
               run r1 { no B and #(iden - (Int -> Int)) = 1 } for exactly 1 A, 1 B, 3 Int\n";
    assert!(!is_sat_cmd(src, 0), "row6b r2 (=2, all-atoms) UNSAT");
    assert!(is_sat_cmd(src, 1), "row6b r1 (=1, live) SAT");
}

/// Row 6b reflexivity control: with `B` genuinely populated (`some B`), `iden`
/// does pick up its live pair, so `#(iden - (Int -> Int)) = 2` is reachable.
/// `run { some B and #(iden - (Int -> Int)) = 2 } for exactly 1 A, 1 B, 3 Int` =
/// **SAT**. Probe: `mt053/ctrl_iden_card_populated.als`.
#[test]
fn row6b_control_populated_sat() {
    let src = "sig A {}\nsig B {}\n\
               run { some B and #(iden - (Int -> Int)) = 2 } for exactly 1 A, 1 B, 3 Int\n";
    assert!(is_sat(src), "row6b control SAT (live B pair counted)");
}

// ================= row 8 — skolem/param domains are live too =================

// -- Row 8a: mt-053 liveness IS threaded through the HO-skolem domain, but the
//    absolute count differs from the jar for an **orthogonal, deliberately
//    deferred** reason (mt-055), so the two facets are pinned separately. --
//
// `run { some p: A -> univ | some p }` over a relation-valued (arity-2) decl.
// mettle reads a **plain-product** arrow quantifier decl (`A -> univ`, no
// multiplicity marks) as *first-order* — `p` ranges over one **pair** at a time
// (implicit `one`), which is verdict-correct and pinned elsewhere (closure.als,
// hotel2.als, `solve.rs`; the SB-0 counting gauge conservatively `skip_ho_skolem`s
// exactly this shape). The jar instead reads it as *higher-order* — `p` ranges
// over any **sub-relation** — so its counts are `2^|A×univ| − 1` (subsets), not
// `|A×univ|` (pairs). Flipping mettle's FO reading to HO is the mt-055 decision,
// **out of mt-053's scope** and left to a dedicated bead/probe (NOTES.md §"Corners
// left unprobed" flags it explicitly).
//
// What mt-053 *does* fix — and what this pair locks in — is that the live union
// (not all-atoms) reaches this path: `p`'s membership/bound tracks `B`'s actual
// per-instance population. Under mettle's FO (one-pair) reading that is directly
// observable: the counts are the *live* pair-counts, strictly below the all-atoms
// pair-counts.

/// mt-053 liveness reaches the HO-skolem domain (regression pin). Under mettle's
/// (verdict-correct) first-order plain-product-arrow reading, `some p: A -> univ`
/// counts *live* pairs `|A × univ(this instance)|`, summed over `B`'s populations:
/// **3** (no B), **7** (1 B = 3+4), **16** (2 B = 3+8+5). The all-atoms `univ`
/// would give **3 / 8 / 20** — so these strictly-smaller counts are the observable
/// proof the live union threads through the skolem membership/bound. (The jar's
/// *higher-order* reading gives 7 / 22 / 68 — see `row8a_jar_ho_reading`, an
/// mt-055 target.) Probes: `mt053/ctrl_ho_skolem_nob.als`,
/// `row8a_ho_skolem_count.als`, `row8a_ho_skolem_scaling.als`.
#[test]
fn row8a_live_univ_threads_skolem_domain() {
    let no_b = "sig A {}\nrun { some p: A -> univ | some p } for exactly 1 A, 1 Int\n";
    let one_b = "sig A {}\nsig B {}\n\
                 run { some p: A -> univ | some p } for exactly 1 A, 1 B, 1 Int\n";
    let two_b = "sig A {}\nsig B {}\n\
                 run { some p: A -> univ | some p } for exactly 1 A, 2 B, 1 Int\n";
    assert_eq!(
        count_at(no_b, 0),
        3,
        "row8a no-B: 3 live pairs (== all-atoms here)"
    );
    assert_eq!(
        count_at(one_b, 0),
        7,
        "row8a 1 B: 7 = 3+4 (live); all-atoms would be 8"
    );
    assert_eq!(
        count_at(two_b, 0),
        16,
        "row8a 2 B: 16 = 3+8+5 (live); all-atoms would be 20"
    );
}

/// The jar's **higher-order** reading of `some p: A -> univ` (subsets, not pairs):
/// **7** (no B), **22** (1 B), **68** (2 B) at SB-0 — jar-verified in NOTES.md and
/// re-verified by the tech lead (68). Ignored: reaching these requires mettle to
/// treat a plain-product arrow quantifier decl as higher-order, which is the
/// **mt-055** decision, orthogonal to mt-053's univ-liveness fix. Unignore when
/// mt-055 lands. Probes: `mt053/ctrl_ho_skolem_nob.als`,
/// `row8a_ho_skolem_count.als`, `row8a_ho_skolem_scaling.als`.
#[test]
#[ignore = "mt-055: plain-product arrow quantifier decl is HO in the jar, FO in mettle"]
fn row8a_jar_ho_reading() {
    let no_b = "sig A {}\nrun { some p: A -> univ | some p } for exactly 1 A, 1 Int\n";
    let one_b = "sig A {}\nsig B {}\n\
                 run { some p: A -> univ | some p } for exactly 1 A, 1 B, 1 Int\n";
    let two_b = "sig A {}\nsig B {}\n\
                 run { some p: A -> univ | some p } for exactly 1 A, 2 B, 1 Int\n";
    assert_eq!(count_at(no_b, 0), 7, "row8a HO no-B SB=0 = 7");
    assert_eq!(count_at(one_b, 0), 22, "row8a HO 1 B SB=0 = 22");
    assert_eq!(count_at(two_b, 0), 68, "row8a HO 2 B SB=0 = 68");
}

/// Row 8b (mt-055 shape, first-order flavor): a scalar `pred P[u: univ]` param,
/// implicitly existentially quantified by `run P`, is also live-restricted. With
/// `B` forced empty by a fact, `b0` is excluded → **UNSAT**. Probe:
/// `mt053/row8b_fo_pred_param_sat.als`.
#[test]
fn row8b_fo_pred_param_unsat() {
    let src = "sig A {}\nsig B {}\nfact { no B }\n\
               pred P[u: univ] { u not in A and u not in Int and u not in String }\n\
               run P for exactly 1 A, 1 B\n";
    assert!(!is_sat(src), "row8b UNSAT (pred-param univ is live)");
}

/// Row 8b reflexivity control: without `no B`, the solver may pick `B = {b0}`, so
/// the implicit `run P` existential reaches SAT. Probe:
/// `mt053/ctrl_predparam_sat.als`.
#[test]
fn row8b_control_predparam_sat() {
    let src = "sig A {}\nsig B {}\n\
               pred P[u: univ] { u not in A and u not in Int and u not in String }\n\
               run P for exactly 1 A, 1 B\n";
    assert!(is_sat(src), "row8b control SAT");
}

// ==================== row 9 — control: univ/iden unmentioned ====================

/// Row 9 (control): a model mentioning neither `univ` nor `iden` is bit-identical
/// to before the live-univ change. The already jar-pinned "twofield" probe:
/// `sig A { f: set A, g: set A } fact { all a: A | lone a.f and lone a.g } run {}
/// for 3` = **4352** at SB-0, **1140** at SB=20. Probe: `mt053/row9_control.als`.
#[test]
fn row9_control_unmentioned_unchanged() {
    let src = "sig A { f: set A, g: set A }\n\
               fact { all a: A | lone a.f and lone a.g }\n\
               run { } for 3\n";
    assert_eq!(count_at(src, 0), 4352, "row9 SB=0 = 4352 (unchanged)");
    assert_eq!(count_at(src, 20), 1140, "row9 SB=20 = 1140 (unchanged)");
}
