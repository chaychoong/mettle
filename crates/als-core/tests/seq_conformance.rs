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
