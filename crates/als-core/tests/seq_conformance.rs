//! `seq`-fidelity conformance (mt-046, LEDGER-008): jar-pinned bounds shape,
//! `maxseq` derivation, the per-owner contiguity fact, the `lone`-value column,
//! and solve-level `util/sequniv` behavior. Jar-free — every expected value is a
//! constant citing its probe row (translation-ref §14 / probes §10.10 Q1–Q4,
//! plus the mt-046 contiguity + stdlib differential probes recorded in §10.10),
//! so CI runs it with no oracle.
//!
//! The pinned facts: `seq/Int` bound to `{0 … maxseq−1}`; a `seq X` field is
//! `seq/Int -> lone X` (stored `owner -> index -> X`, arity 3, index column
//! bounded by `seq/Int`); the contiguity fact `dom(f) − dom(f).(Int/next) ⊆
//! Int/zero` is **per-owner** (jar-verified probe mt046-contig: two owners using
//! indices {0,1} and {1} → UNSAT); `maxseq` = `min(overall, 2^{w−1}−1)` (4 with
//! no overall), set directly by `for N seq`. The `util/sequniv` differential
//! rows pin the clean-room body fixes (idxOf/lastIdxOf first/last direction;
//! `afterLastIdx[empty] = 0`).

use als_core::bounds::{RelBound, TupleSet};
use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, BoundsResult, ScopedUniverse,
    SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};
use std::collections::BTreeSet;

/// Computes the scoped universe of command 0.
fn scoped(src: &str) -> ScopedUniverse {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    compute_universe(&world, &graph, &world.commands[0]).expect("universe")
}

/// `maxseq` derived for command 0.
fn maxseq(src: &str) -> u32 {
    scoped(src).maxseq
}

/// Solves command 0 under the canonical (forbid-overflow) options; `true` = SAT.
/// Panics on a typed defer — every model here is expected to lower fully.
fn solve(src: &str) -> bool {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let su = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &su, &mut ir);
    let goal = lower_command(&world, &graph, &su, &bounds, &mut ir, 0).expect("lower");
    match solve_goal(&ir, &su, &goal, &bounds, &SolveOptions::default()) {
        Ok(SolveVerdict::Sat(_)) => true,
        Ok(SolveVerdict::Unsat) => false,
        Ok(SolveVerdict::Unknown) => panic!("unbudgeted solve returned Unknown"),
        Err(e) => panic!("unexpected solve defer: {e:?}"),
    }
}

/// A fully built command, for inspecting a field relation's bounds.
struct Built {
    ir: Ir,
    result: BoundsResult,
}

fn build(src: &str) -> Built {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let su = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let result = compute_bounds(&world, &su, &mut ir);
    Built { ir, result }
}

impl Built {
    /// The bound of the field relation named `name` (e.g. `P.f`).
    fn field_bound(&self, name: &str) -> &RelBound {
        let rel = self
            .ir
            .relations
            .iter()
            .find(|(_, r)| r.name == name)
            .unwrap_or_else(|| {
                panic!(
                    "no relation `{name}`; have {:?}",
                    self.ir
                        .relations
                        .iter()
                        .map(|(_, r)| r.name.clone())
                        .collect::<Vec<_>>()
                )
            })
            .0;
        self.result.bounds.get(rel).expect("bound")
    }

    /// The distinct atom names appearing in column `col` of `ts`.
    fn column_names(&self, ts: &TupleSet, col: usize) -> BTreeSet<String> {
        ts.iter()
            .map(|t| self.result.bounds.universe.name(t.atoms()[col]).to_owned())
            .collect()
    }
}

// ------------------------------- Q1: field desugar --------------------------

#[test]
fn q1_seq_field_is_arity3_indexed_by_seq_int() {
    // Probe Q1: `sig P { f: seq Int }` for `2 but 3 seq, 4 int` → the stored
    // relation is arity 3 (`owner -> index -> value`), the index column upper is
    // exactly the `seq/Int` atoms {0,1,2}, and the upper = P × {0,1,2} × ints.
    let b = build("sig P { f: seq Int }\nrun {} for 2 but 3 seq, 4 int\n");
    let up = b.field_bound("this/P.f").upper();
    assert_eq!(up.arity(), 3, "seq field is owner -> index -> value");
    // Index column (column 1) is bounded by the seq/Int atoms {0,1,2}.
    assert_eq!(
        b.column_names(up, 1),
        ["0", "1", "2"].iter().map(|s| (*s).to_owned()).collect(),
    );
    // Value column (column 2) ranges over every int atom.
    assert_eq!(b.column_names(up, 2).len(), 16, "Int column = 16 atoms");
    // upper = |P upper (2)| × |seq/Int (3)| × |Int (16)|.
    assert_eq!(up.len(), 2 * 3 * 16);
}

// ------------------------------- Q2/Q3: contiguity --------------------------

#[test]
fn q2_gap_in_indices_is_unsat() {
    // Probe Q2: a seq using index 1 without index 0 is UNSAT — the contiguity
    // fact forces the used indices to be a prefix from 0.
    assert!(!solve(
        "sig X {}\none sig P { f: seq X }\nrun { some (1.(P.f)) and no (0.(P.f)) } for 2 but 3 seq, 2 X\n"
    ));
}

#[test]
fn q3_prefix_indices_is_sat() {
    // Probe Q3: indices 0 and 1 both used (a proper prefix) is SAT.
    assert!(solve(
        "sig X {}\none sig P { f: seq X }\nrun { some (0.(P.f)) and some (1.(P.f)) } for 2 but 3 seq, 2 X\n"
    ));
}

#[test]
fn contiguity_is_per_owner_not_global() {
    // Probe mt046-contig (the deciding per-owner-vs-global probe): two owners,
    // one using indices {0,1}, the other using {1} without {0}. Global
    // contiguity (union {0,1} is a prefix) would be SAT; per-owner contiguity
    // (the second owner violates) is UNSAT. The jar is UNSAT → PER-OWNER.
    let two_owners = |p2: &str| {
        format!(
            "sig X {{}}\nsig P {{ f: seq X }}\n\
             run {{ some disj p1, p2: P |\n\
               (some p1.f[0]) and (some p1.f[1]) and {p2} }} for 2 but 3 seq, 2 X\n"
        )
    };
    // p2 uses index 1 without 0 → UNSAT (per-owner).
    assert!(!solve(&two_owners("(no p2.f[0]) and (some p2.f[1])")));
    // Control: p2 uses index 0 only (a valid prefix) → SAT.
    assert!(solve(&two_owners("(some p2.f[0]) and (no p2.f[1])")));
}

// ------------------------------- lone-value column --------------------------

#[test]
fn lone_value_two_values_per_index_is_unsat() {
    // The `lone` on the value column: one owner+index mapped to two distinct
    // values is UNSAT. `0.(P.f) = X` with `#X = 2` forces index 0 to hold both X
    // atoms → violates `lone i.(P.f)`.
    assert!(!solve(
        "sig X {}\none sig P { f: seq X }\nrun { 0.(P.f) = X and #X = 2 } for 2 but 3 seq, 2 X\n"
    ));
    // Control: index 0 holds exactly one value → SAT.
    assert!(solve(
        "sig X {}\none sig P { f: seq X }\nrun { one 0.(P.f) and #X = 2 } for 2 but 3 seq, 2 X\n"
    ));
}

// ------------------------------- Q4: maxseq ---------------------------------

#[test]
fn q4_maxseq_derivation() {
    // Probe Q4: `for N` sets maxseq to the overall (2, 6); `for N seq` sets it
    // directly (5), independent of overall; no scope defaults to 4; and it is
    // clamped to `2^{w−1}−1` (bitwidth 3 → 3).
    assert_eq!(maxseq("sig A {}\nrun {} for 2\n"), 2, "for 2");
    assert_eq!(maxseq("sig A {}\nrun {} for 6\n"), 6, "for 6");
    assert_eq!(
        maxseq("sig A {}\nrun {} for 2 but 5 seq\n"),
        5,
        "for 2 but 5 seq (independent of overall)"
    );
    assert_eq!(maxseq("sig A {}\nrun {}\n"), 4, "no scope → 4");
    assert_eq!(
        maxseq("sig A {}\nrun {} for 6 but 3 int\n"),
        3,
        "clamped to max(bitwidth 3) = 3"
    );
}

// ------------------------------- util/sequniv differential ------------------
// These pin the clean-room body semantics of util/sequniv against the jar
// (mt-046 differential probes, §10.10): each verdict was confirmed against
// Alloy 6.2.0. Two of them are regressions for the clean-room bugs mt-046 fixed
// (idxOf/lastIdxOf direction swap; `afterLastIdx[empty]`).

#[test]
fn sequniv_elems_and_inds() {
    // `elems[P.f] = X` with `#X = 2` (both X atoms appear) is SAT; `#inds` of a
    // used-2-index seq is 2.
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\nrun { elems[P.f] = X and #X = 2 } for 2 but 3 seq, 2 X\n"
    ));
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\nrun { #inds[P.f] = 2 } for 2 but 3 seq, 2 X\n"
    ));
}

#[test]
fn sequniv_lastidx_is_max_index() {
    // `lastIdx` of a length-3 seq is 2 (SAT); it is never 3 (UNSAT), since the
    // used indices are {0,1,2}.
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\nrun { #P.f = 3 and lastIdx[P.f] = 2 } for 3 but 3 seq, 2 X\n"
    ));
    assert!(!solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\nrun { #P.f = 3 and lastIdx[P.f] = 3 } for 3 but 3 seq, 2 X\n"
    ));
}

#[test]
fn sequniv_idxof_lastidxof_direction() {
    // Regression for the clean-room swap fix (mt-046): for `a` at indices {0,2},
    // `idxOf` = the FIRST index 0 and `lastIdxOf` = the LAST index 2 (jar). The
    // pre-fix bodies gave the reverse (idxOf=2, lastIdxOf=0), which was UNSAT.
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\n\
         run { some disj a,b: X | P.f = (0->a)+(1->b)+(2->a) and idxOf[P.f,a]=0 and lastIdxOf[P.f,a]=2 } for 2 but 3 seq, 2 X\n"
    ));
    // The reversed values are UNSAT (proving idxOf ≠ lastIdxOf here).
    assert!(!solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\n\
         run { some disj a,b: X | P.f = (0->a)+(1->b)+(2->a) and idxOf[P.f,a]=2 } for 2 but 3 seq, 2 X\n"
    ));
}

#[test]
fn sequniv_add_to_empty_is_length_one() {
    // Regression for the `afterLastIdx[empty] = 0` fix (mt-046): adding to an
    // empty sequence yields a length-1 sequence `{0 -> e}` (jar SAT). The pre-fix
    // `afterLastIdx[empty] = none` left `add` a no-op (UNSAT).
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\nrun { no P.f and (some e: X | #add[P.f,e] = 1) } for 2 but 3 seq, 2 X\n"
    ));
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\n\
         run { some e: X | let s2 = add[P.f, e] | last[s2] = e and #s2 = 1 } for 2 but 3 seq, 2 X\n"
    ));
}

#[test]
fn sequniv_afterlastidx_is_min_unused() {
    // probes mt046-noncontig / mt046-full: `afterLastIdx` is the smallest
    // UNUSED `seq/Int` index, NOT `lastIdx.next` — for the gapped `{1->e}` it
    // is 0 (not 2), and a full sequence has no after-index at all. sequniv funs
    // accept arbitrary `Int -> univ` relations, so the gapped case is reachable.
    assert!(solve(
        "open util/sequniv as sq\nsig E {}\nrun { some e: E | sq/afterLastIdx[1->e] = 0 } for 3 but 4 Int\n"
    ));
    assert!(!solve(
        "open util/sequniv as sq\nsig E {}\nrun { some e: E | sq/afterLastIdx[1->e] = 2 } for 3 but 4 Int\n"
    ));
    assert!(solve(
        "open util/sequniv as sq\nsig E {}\nrun { some e: E | no sq/afterLastIdx[(0->e)+(1->e)+(2->e)] } for 3 but 4 Int\n"
    ));
    assert!(!solve(
        "open util/sequniv as sq\nsig E {}\nrun { some e: E | sq/afterLastIdx[(0->e)+(1->e)+(2->e)] = 3 } for 3 but 4 Int\n"
    ));
}

// ------------------- mt-084: the shift funs' result index --------------------
// The clean-room bodies let a shifted result index escape `seq/Int`: `rest`
// produced a tuple at −1 and `insert`/`append` one past the end. Since a `seq X`
// field is indexed by `seq/Int`, such a result can never equal one, which turned
// `correctChord.als` rows [19]–[21]/[24] into spurious UNSAT and row [30] into a
// spurious counterexample (a disequality against `insert[…]` became a tautology).
// A second defect in the same fun: the shift term was keyed on `gte`, so index
// `i` carried both `e` and the old `s[i−1]`.
//
// Every expected value below is a jar constant from the mt-084 P1/P2/P3 probes
// (`EvalProbe` ground evaluation, `for 3 but 3 seq`), recorded in
// `scratchpad/probe/mt084/NOTES.md`. Jar-free at test time.

/// Preamble giving three named element atoms plus `ui/negate` for negative
/// index literals (probe hygiene: never a bare `0-N`, which is set difference).
const SEQUNIV_GROUND: &str = "open util/sequniv as sq\nopen util/integer as ui\n\
     abstract sig E {}\none sig A, B, C extends E {}\n";

/// Solves a ground `util/sequniv` body at `3 seq`, so `seq/Int` = {0,1,2} and
/// `(0->A)+(1->B)+(2->C)` is a full sequence.
fn sequniv_ground(body: &str) -> bool {
    solve(&format!(
        "{SEQUNIV_GROUND}run {{ {body} }} for 3 but 3 seq\n"
    ))
}

#[test]
fn sequniv_shift_funs_clamp_result_index_to_seq_int() {
    // P2/P3: `rest`, `insert`, `append` and `subseq` drop any result tuple whose
    // index leaves `seq/Int`.
    assert!(sequniv_ground(
        "sq/insert[(0->A)+(1->B)+(2->C), 0, C] = (0->C)+(1->A)+(2->B)"
    ));
    assert!(sequniv_ground(
        "sq/rest[(0->A)+(1->B)+(2->C)] = (0->B)+(1->C)"
    ));
    assert!(sequniv_ground(
        "sq/append[(0->A)+(1->B), (0->A)+(1->B)] = (0->A)+(1->B)+(2->A)"
    ));
    assert!(sequniv_ground(
        "sq/subseq[(0->A)+(1->B)+(2->C), ui/negate[1], 2] = (1->A)+(2->B)"
    ));
    // Negative space — pre-fix each of these carried the escaped tuple and so
    // was SAT, which is exactly what made the equalities above UNSAT.
    assert!(!sequniv_ground(
        "some i: Int | i in sq/insert[(0->A)+(1->B)+(2->C), 0, C].univ and i not in seq/Int"
    ));
    assert!(!sequniv_ground(
        "some i: Int | i in sq/rest[(0->A)+(1->B)+(2->C)].univ and i not in seq/Int"
    ));
    assert!(!sequniv_ground(
        "some i: Int | i in sq/append[(0->A)+(1->B), (0->A)+(1->B)].univ and i not in seq/Int"
    ));
}

#[test]
fn sequniv_delete_and_setat_do_not_clamp() {
    // P3 negative space: the clamp is per-fun, NOT a blanket intersection of
    // every sequniv result with `seq/Int -> univ`. `delete` and `setAt` keep
    // out-of-domain result indices where `rest`/`insert` drop them.
    assert!(sequniv_ground(
        "sq/delete[(0->A)+(1->B)+(2->C), ui/negate[1]] = (ui/negate[1]->A)+(0->B)+(1->C)"
    ));
    assert!(sequniv_ground(
        "sq/setAt[(0->A)+(1->B)+(2->C), 5, A] = (0->A)+(1->B)+(2->C)+(5->A)"
    ));
    // The decisive pair: same 5-tuple input, index 3 kept by `delete`…
    assert!(sequniv_ground(
        "sq/delete[(0->A)+(1->B)+(2->C)+(3->A)+(4->B), 0] = (0->B)+(1->C)+(2->A)+(3->B)"
    ));
    // …and dropped by its mirror image `rest`.
    assert!(sequniv_ground(
        "sq/rest[(0->A)+(1->B)+(2->C)+(3->A)+(4->B)] = (0->B)+(1->C)+(2->A)"
    ));
}

#[test]
fn sequniv_insert_shifts_strictly_past_the_index() {
    // P2/P3: the shift term is `gt`, not `gte`.
    assert!(sequniv_ground(
        "sq/insert[(0->A)+(1->B), 1, C] = (0->A)+(1->C)+(2->B)"
    ));
    // Pre-fix index 1 held both `C` and the old `A`, so the result was not even
    // a function and no `seq` field could equal it.
    assert!(!sequniv_ground(
        "some i: seq/Int | not lone i.(sq/insert[(0->A)+(1->B), 1, C])"
    ));
    // An out-of-range `i` contributes nothing, yet a negative `i` still shifts:
    // the clamp is on the index domain, not a guard on `i`.
    assert!(sequniv_ground(
        "sq/insert[(0->A)+(1->B), 3, C] = (0->A)+(1->B)"
    ));
    assert!(sequniv_ground(
        "sq/insert[(0->A)+(1->B), ui/negate[1], C] = (1->A)+(2->B)"
    ));
    // A gapped input pins the three-way body shape (nothing shifts into 2,
    // because `s[1]` is empty).
    assert!(sequniv_ground(
        "sq/insert[(0->A)+(2->C), 1, B] = (0->A)+(1->B)"
    ));
}

#[test]
fn sequniv_shifted_result_is_assignable_to_a_seq_field() {
    // mt-084 wrong-UNSAT polarity, probe P1 rows 6 and 7 (jar SAT, mettle UNSAT
    // pre-fix): the two shapes `correctChord.als` builds a successor list with —
    // `insert[list, 0, e]` (rows [20]/[21]/[24]) and `add[rest[list], e]`
    // (row [19]). Both must be equatable with another `seq` field.
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\nsig Q { g: seq X }\n\
         run { #P.f = 3 and (some q: Q, e: X | q.g = insert[P.f, 0, e]) } for 3 but 3 seq, 3 X, 2 Q\n"
    ));
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\nsig Q { g: seq X }\n\
         run { #P.f = 3 and (some q: Q, e: X | q.g = add[rest[P.f], e]) } for 3 but 3 seq, 3 X, 2 Q\n"
    ));
    // Probe P1 rows 0 and 1: inserting into a full sequence keeps it length 3,
    // and can never make it length 4.
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\n\
         run { #P.f = 3 and (some e: X | #insert[P.f, 0, e] = 3) } for 3 but 3 seq, 3 X\n"
    ));
    assert!(!solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\n\
         run { #P.f = 3 and (some e: X | #insert[P.f, 0, e] = 4) } for 3 but 3 seq, 3 X\n"
    ));
}

#[test]
fn sequniv_insert_result_can_equal_its_own_seq_field() {
    // mt-084 wrong-SAT polarity (`correctChord.als` row [30]): that check asserts
    // `field != insert[…]`, which pre-fix was a TAUTOLOGY — a 4-tuple result can
    // never equal a 3-tuple `seq` field — so "a change is enabled" held even in a
    // state where it should not, and the check reported a spurious counterexample.
    // Stated positively here: the equality must be satisfiable (a constant list
    // is its own 0-insert of its element). Pre-fix this was UNSAT.
    assert!(solve(
        "open util/sequniv\nsig X {}\none sig P { f: seq X }\n\
         run { #P.f = 3 and (some e: X | P.f = insert[P.f, 0, e]) } for 3 but 3 seq, 3 X\n"
    ));
}

// ---------------------- mt-084: the same defects in seqrel -------------------
// `util/seqrel` indexes by an ordered `SeqIdx` sig, so nothing can escape the
// index domain — but it carried the same `gte` shift defect PLUS a second one:
// its shifted lookup was spelled `j.(ord/prev) -> x in s`, and at the boundary
// the step is empty, making `none -> x in s` vacuously true and putting EVERY
// element at that index. Values are jar constants from probe P4.

/// Preamble reaching the three `SeqIdx` atoms through funs — mettle's evaluator
/// cannot resolve module-qualified atom literals, so naming them this way is
/// what let the same probe text run against both the jar and mettle.
const SEQREL_GROUND: &str = "open util/seqrel[E] as sr\n\
     abstract sig E {}\none sig A, B, C extends E {}\n\
     fun i0: set sr/SeqIdx { sr/firstIdx }\n\
     fun i1: set sr/SeqIdx { sr/SeqIdx - sr/firstIdx - sr/finalIdx }\n\
     fun i2: set sr/SeqIdx { sr/finalIdx }\n";

/// Solves a ground `util/seqrel` body over a 3-atom `SeqIdx` order.
fn seqrel_ground(body: &str) -> bool {
    solve(&format!("{SEQREL_GROUND}run {{ {body} }} for 3\n"))
}

#[test]
fn seqrel_insert_shifts_strictly_past_the_index() {
    assert!(seqrel_ground(
        "sr/insert[(i0->A)+(i1->B), i1, C] = (i0->A)+(i1->C)+(i2->B)"
    ));
    assert!(seqrel_ground(
        "sr/insert[(i0->A)+(i1->B), i0, C] = (i0->C)+(i1->A)+(i2->B)"
    ));
    assert!(seqrel_ground(
        "sr/insert[(i0->A)+(i2->C), i1, B] = (i0->A)+(i1->B)"
    ));
}

#[test]
fn seqrel_shift_lookup_is_empty_at_the_order_boundary() {
    assert!(seqrel_ground(
        "sr/rest[(i0->A)+(i1->B)+(i2->C)] = (i0->B)+(i1->C)"
    ));
    assert!(seqrel_ground(
        "sr/delete[(i0->A)+(i1->B)+(i2->C), i1] = (i0->A)+(i1->C)"
    ));
    // Negative space for the vacuous-`in` defect: pre-fix the boundary index
    // held all three elements at once.
    assert!(!seqrel_ground(
        "some i: sr/SeqIdx | not lone i.(sr/rest[(i0->A)+(i1->B)+(i2->C)])"
    ));
    assert!(!seqrel_ground(
        "some i: sr/SeqIdx | not lone i.(sr/delete[(i0->A)+(i1->B)+(i2->C), i1])"
    ));
}

// --------------------- mt-085: the same defects in sequence ------------------
// `util/sequence` carried the mt-084 pair a third time — `rest`'s and `insert`'s
// shifted lookups were spelled `i.(ord/next) -> e in s.seqElems`, vacuously true
// at the order boundary, and `insert` shifted on `gte`. Because this module's
// operations are PREDS relating an input and an output `Seq` atom whose field is
// `SeqIdx -> lone elem`, the vacuous term made the whole pred unsatisfiable
// rather than merely wrong-valued.
//
// The jar round that pinned it (`scratchpad/probe/mt085/`) also found that these
// preds are TOTAL nowhere: `rest` of an empty sequence, `add`/`insert` without
// room, an overflowing `append`, and an out-of-range or inverted `subseq` window
// are all UNSAT in the jar, where the clean-room comprehensions silently
// truncated. Every expected value below is a jar constant from those probes
// (`EvalProbe`, `for 3 but 5 Seq`). Jar-free at test time.

/// Three named element atoms, three named `SeqIdx` handles reached through the
/// root's own `open util/ordering[SeqIdx]` (Alloy shares one module instance per
/// parameter, so `o/next` is `sq`'s own order), and one `H` atom holding the
/// input/output `Seq` handles.
const SEQUENCE_GROUND: &str = "open util/sequence[E] as sq\nopen util/ordering[SeqIdx] as o\n\
     abstract sig E {}\none sig A, B, C extends E {}\n\
     one sig H { s: one Seq, t: one Seq, r: one Seq }\n\
     fun i0: SeqIdx { o/first }\n\
     fun i1: SeqIdx { o/first.(o/next) }\n\
     fun i2: SeqIdx { o/first.(o/next).(o/next) }\n";

/// Solves a ground `util/sequence` body over a 3-atom `SeqIdx` order with room
/// for five distinct `Seq` atoms — the probe scope.
fn sequence_ground(body: &str) -> bool {
    solve(&format!(
        "{SEQUENCE_GROUND}run {{ {body} }} for 3 but 5 Seq\n"
    ))
}

#[test]
fn sequence_rest_shift_lookup_is_empty_at_the_order_boundary() {
    // Probe mt085-p1 rows 0/1/2. Pre-fix all three were UNSAT: `none -> e in
    // s.seqElems` is vacuously true, so the last index held A, B and C at once,
    // which `seqElems: SeqIdx -> lone elem` forbids. Note row 2 — a single
    // element is NOT immune here, contra the mt-084 P4 prediction, because the
    // spurious `{i2->A}` also breaks the contiguous-prefix sig fact.
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/rest[H.s, H.r] and H.r.seqElems = i0->B + i1->C"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B and sq/rest[H.s, H.r] and H.r.seqElems = i0->B"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A and sq/rest[H.s, H.r] and no H.r.seqElems"
    ));
    // Negative space (row 3): `rest` of an empty sequence is FALSE, not a
    // no-op — the opposite polarity, and the pre-fix `isEmpty[s] => isEmpty[r]`
    // branch made it SAT.
    assert!(!sequence_ground("no H.s.seqElems and sq/rest[H.s, H.r]"));
}

#[test]
fn sequence_insert_shifts_strictly_past_the_index() {
    // Probe mt085-p1 rows 4/5/6/9 and mt085-p2 row 2. Pre-fix every one was
    // UNSAT: `gte` put both the new element and the shifted old one at `idx`,
    // and at `idx = ord/first` the `-> x in` lookup was additionally vacuous.
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B and sq/insert[H.s, i0, C, H.r] \
         and H.r.seqElems = i0->C + i1->A + i2->B"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B and sq/insert[H.s, i1, C, H.r] \
         and H.r.seqElems = i0->A + i1->C + i2->B"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B and sq/insert[H.s, i2, C, H.r] \
         and H.r.seqElems = i0->A + i1->B + i2->C"
    ));
    assert!(sequence_ground(
        "no H.s.seqElems and sq/insert[H.s, i0, A, H.r] and H.r.seqElems = i0->A"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A and sq/insert[H.s, i1, B, H.r] and H.r.seqElems = i0->A + i1->B"
    ));
    // Duplicates are preserved, not collapsed (mt085-p2 row 3).
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->A and sq/insert[H.s, i0, A, H.r] \
         and H.r.seqElems = i0->A + i1->A + i2->A"
    ));
}

#[test]
fn sequence_insert_and_add_need_room() {
    // mt085-p1 row 7 and mt085-p2 rows 0/1: inserting anywhere into a FULL
    // sequence is UNSAT — the jar does not truncate the way util/sequniv's
    // `insert` does. Pre-fix, `insert` at a middle index of a full sequence was
    // SAT with a silently truncated result.
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/insert[H.s, i0, A, H.r]"
    ));
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/insert[H.s, i1, A, H.r]"
    ));
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/insert[H.s, i2, A, H.r]"
    ));
    // mt085-p1 row 8: an index past `afterLastIdx` is rejected outright.
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A and sq/insert[H.s, i2, B, H.r]"
    ));
    // mt085-p1 row 14: `add` to a full sequence is UNSAT, not the no-op that
    // dropping `none -> e` produced pre-fix. Row 13 is the positive control.
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/add[H.s, A, H.r]"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A and sq/add[H.s, B, H.r] and H.r.seqElems = i0->A + i1->B"
    ));
}

#[test]
fn sequence_setat_extends_at_the_first_free_index() {
    // mt085-p2 rows 18/19: `setAt`'s guard is `inds + afterLastIdx`, the same as
    // `insert`'s — writing at the first FREE index appends. The pre-fix `idx in
    // inds[s]` guard made both of these UNSAT.
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B and sq/setAt[H.s, i2, C, H.r] \
         and H.r.seqElems = i0->A + i1->B + i2->C"
    ));
    assert!(sequence_ground(
        "no H.s.seqElems and sq/setAt[H.s, i0, A, H.r] and H.r.seqElems = i0->A"
    ));
    // Negative space (mt085-p1 row 16): one past that is still rejected, so the
    // guard is not simply dropped.
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A and sq/setAt[H.s, i2, B, H.r]"
    ));
    // Overwriting in place is unaffected (mt085-p1 row 15).
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/setAt[H.s, i1, A, H.r] \
         and H.r.seqElems = i0->A + i1->A + i2->C"
    ));
}

#[test]
fn sequence_append_must_fit_end_to_end() {
    // mt085-p1 rows 19/20: an append that would run past the last `SeqIdx` is
    // UNSAT. Pre-fix both were SAT with a truncated result, and row 20 (a FULL
    // first argument, whose `afterLastIdx` is empty so `#(ord/prevs[none])` is
    // 0) silently restarted the second sequence at index 0 on top of the first.
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B and H.t.seqElems = i0->C + i1->A and sq/append[H.s, H.t, H.r]"
    ));
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and H.t.seqElems = i0->A \
         and sq/append[H.s, H.t, H.r]"
    ));
    // Positive controls: mt085-p1 row 18 and mt085-p2 row 5 fit exactly.
    assert!(sequence_ground(
        "H.s.seqElems = i0->A and H.t.seqElems = i0->B + i1->C and sq/append[H.s, H.t, H.r] \
         and H.r.seqElems = i0->A + i1->B + i2->C"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B and H.t.seqElems = i0->C and sq/append[H.s, H.t, H.r] \
         and H.r.seqElems = i0->A + i1->B + i2->C"
    ));
}

#[test]
fn sequence_subseq_window_must_be_occupied_and_ordered() {
    // mt085-p1 row 24 and mt085-p2 rows 9/11: an inverted window, a `to` past
    // the end, and any window on an empty sequence are all UNSAT — pre-fix each
    // was SAT, quietly yielding a clamped or empty result.
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/subseq[H.s, H.r, i2, i0]"
    ));
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B and sq/subseq[H.s, H.r, i0, i2]"
    ));
    assert!(!sequence_ground(
        "no H.s.seqElems and sq/subseq[H.s, H.r, i0, i0]"
    ));
    // Positive controls (mt085-p1 rows 22/23, mt085-p2 row 8).
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/subseq[H.s, H.r, i1, i2] \
         and H.r.seqElems = i0->B + i1->C"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/subseq[H.s, H.r, i1, i1] \
         and H.r.seqElems = i0->B"
    ));
}

#[test]
fn sequence_copy_constrains_only_the_landing_range() {
    // mt085-p2 rows 13/14/16: `copy` is a one-way constraint, not an equality —
    // it pins `dest` where the copy lands and leaves the rest of `dest` free, so
    // its output is deliberately NON-unique (row 14 is SAT, unlike every other
    // operation's uniqueness probe). The pre-fix equality body made all of these
    // UNSAT.
    assert!(sequence_ground(
        "H.s.seqElems = i0->A and sq/copy[H.s, H.r, i0] and H.r.seqElems = i0->A + i1->B"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A and (some disj r1, r2: Seq | sq/copy[H.s, r1, i0] and sq/copy[H.s, r2, i0])"
    ));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A and sq/copy[H.s, H.r, i1] and H.r.seqElems = i0->C + i1->A"
    ));
    // Negative space: "free outside the landing range" is not "free anywhere" —
    // a wrong value INSIDE the range is still rejected (mt085-p7 row 11), and a
    // copy that would run past the last index is UNSAT rather than truncated
    // (mt085-p1 row 28).
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B and sq/copy[H.s, H.r, i0] and H.r.seqElems = i0->B + i1->A"
    ));
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/copy[H.s, H.r, i1]"
    ));
}

#[test]
fn sequence_hasdups_is_per_sequence() {
    // mt085-p2 rows 25/26. Pre-fix `hasDups` went through a `Seq`-receiver
    // `noDuplicates` whose body read the bare field `seqElems` — the WHOLE
    // `Seq -> SeqIdx -> elem` relation, not `this.seqElems` — so a
    // duplicate-free sequence still "had duplicates" as soon as a second `Seq`
    // atom shared an element with it.
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->A and sq/hasDups[H.s]"
    ));
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/hasDups[H.s]"
    ));
}

#[test]
fn sequence_zero_ary_preds_are_global() {
    // §7.5 and probe mt085-p3: `noDuplicates` / `allExist` /
    // `allExistNoDuplicates` are 0-ARY, not `Seq`-receiver preds. The jar
    // type-rejects every receiver-style call and accepts only the bare name, so
    // pre-fix — where they were declared `pred Seq.noDuplicates ()` — the bodies
    // below did not even resolve.
    //
    // `noDuplicates` binds every `Seq` atom (mt085-p3 rows 1/2, and row 6 with
    // a single `Seq` atom in scope).
    assert!(!sequence_ground(
        "H.s.seqElems = i0->A + i1->A and sq/noDuplicates"
    ));
    assert!(sequence_ground("H.s.seqElems = i0->A + i1->A"));
    assert!(sequence_ground(
        "H.s.seqElems = i0->A + i1->B + i2->C and sq/noDuplicates"
    ));
}

#[test]
fn sequence_allexist_realises_every_sequence() {
    // Probe mt085-p5, the exact-scope counting round: with `canonicalizeSeqs`
    // supplying uniqueness, `allExist` supplies EXISTENCE — every sequence over
    // (`SeqIdx`, `elem`) is realised by some `Seq` atom, so the model is
    // satisfiable at exactly `sum_{j=0..k} n^j` atoms and UNSAT one below it.
    // For k = 2 indices, n = 2 elems that count is 7; for n = 1 it is 3.
    //
    // These scopes must be `exactly` on all three sigs: `util/ordering` already
    // pins `SeqIdx`, but a loose `elem` scope lets the solver shrink the
    // universe and everything comes back SAT regardless (probe round 4).
    let allexist = |scope: &str| {
        solve(&format!(
            "open util/sequence[E] as sq\nsig E {{}}\nrun {{ sq/allExist }} for 6 int, {scope}\n"
        ))
    };
    assert!(allexist("exactly 2 SeqIdx, exactly 2 E, exactly 7 Seq"));
    assert!(!allexist("exactly 2 SeqIdx, exactly 2 E, exactly 6 Seq"));
    assert!(allexist("exactly 2 SeqIdx, exactly 1 E, exactly 3 Seq"));
    assert!(!allexist("exactly 2 SeqIdx, exactly 1 E, exactly 2 Seq"));

    // `allExistNoDuplicates` is the same closure restricted to duplicate-free
    // sequences (5 of them at k = n = 2) AND `noDuplicates` on top — without the
    // second conjunct, five duplicate-free atoms plus one duplicate-carrying one
    // would satisfy `exactly 6 Seq`, which the jar reports UNSAT.
    let aend = |scope: &str| {
        solve(&format!(
            "open util/sequence[E] as sq\nsig E {{}}\n\
             run {{ sq/allExistNoDuplicates }} for 6 int, {scope}\n"
        ))
    };
    assert!(aend("exactly 2 SeqIdx, exactly 2 E, exactly 5 Seq"));
    assert!(!aend("exactly 2 SeqIdx, exactly 2 E, exactly 4 Seq"));
    assert!(!aend("exactly 2 SeqIdx, exactly 2 E, exactly 6 Seq"));

    // The control that makes the counts above meaningful: without the pred,
    // 6 atoms are fine (`canonicalizeSeqs` only caps the count at 7) and 8 are
    // not (mt085-p5 rows 16/17).
    let plain = |scope: &str| {
        solve(&format!(
            "open util/sequence[E] as sq\nsig E {{}}\nrun {{}} for 6 int, {scope}\n"
        ))
    };
    assert!(plain("exactly 2 SeqIdx, exactly 2 E, exactly 6 Seq"));
    assert!(!plain("exactly 2 SeqIdx, exactly 2 E, exactly 8 Seq"));
}
