//! Encoder↔evaluator differential (mt-034, ADR-0011 decision 5): the strongest
//! self-check net. For each small hand model we **brute-force** every candidate
//! instance — every subset assignment of each relation's floating tuples — and
//! count those the [`Evaluator`] accepts (`goal ∧ ¬overflow`, translation-ref
//! §2.4/§6); we assert that count equals the SB-0 model count the mt-033
//! [`enumerate`]r reports. The evaluator and the SAT encoder are two *independent*
//! implementations of the same three-sorted semantics, so their exact counts
//! agreeing over a spread of operators (quantifiers, closure, subset sigs, field
//! multiplicities, cardinality/int-compare, override, restriction, transpose,
//! comprehension) is the real correctness gauge — neither can hide a bug the
//! other lacks.
//!
//! Universes are kept tiny (≤ ~14 floating primary variables) so the `2^k`
//! brute force stays cheap and deterministic.

use als_core::bounds::{Tuple, TupleSet, Universe};
use als_core::ir::{Ir, RelId};
use als_core::{
    compute_bounds, compute_universe, enumerate, lower_command, BoundsResult, Evaluator, Instance,
    LoweredGoal, ScopedUniverse, SolveOptions,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// The floating-tuple layout of one command's bounds: per relation, its fixed
/// lower tuples plus the tuples the solver may add (`upper ∖ lower`).
struct Layout {
    rels: Vec<(RelId, TupleSet, Vec<Tuple>)>,
    universe: Universe,
    total_floating: usize,
}

fn build(src: &str, idx: usize) -> (Ir, ScopedUniverse, LoweredGoal, BoundsResult, Layout) {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[idx]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, idx).expect("lower");

    let mut rels = Vec::new();
    let mut total_floating = 0usize;
    for (rel, bound) in bounds.bounds.iter() {
        let mut floating = Vec::new();
        for t in bound.upper().iter() {
            if !bound.lower().contains(t) {
                floating.push(t.clone());
            }
        }
        total_floating += floating.len();
        rels.push((rel, bound.lower().clone(), floating));
    }
    let layout = Layout {
        rels,
        universe: bounds.bounds.universe.clone(),
        total_floating,
    };
    (ir, scoped, goal, bounds, layout)
}

/// Builds the candidate instance for one bitmask over the flattened floating
/// tuples (relation order, then tuple order within a relation).
fn instance_for(layout: &Layout, mask: u64) -> Instance {
    let mut bit = 0usize;
    let rels = layout.rels.iter().map(|(rel, lower, floating)| {
        let mut ts = lower.clone();
        for t in floating {
            if (mask >> bit) & 1 == 1 {
                ts.insert(t.clone());
            }
            bit += 1;
        }
        (*rel, ts)
    });
    Instance::from_relations(layout.universe.clone(), rels.collect::<Vec<_>>())
}

/// The number of candidate instances the **evaluator** accepts (brute force).
fn evaluator_count(
    ir: &Ir,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    layout: &Layout,
    opts: &SolveOptions,
) -> usize {
    assert!(
        layout.total_floating <= 22,
        "brute force too wide: {} floating vars",
        layout.total_floating
    );
    let mut count = 0usize;
    for mask in 0..(1u64 << layout.total_floating) {
        let inst = instance_for(layout, mask);
        let mut ev = Evaluator::new(ir, &inst, scoped, opts, goal.int_sig, goal.seq_int_sig);
        if ev.accepts(goal.goal).expect("evaluable goal") {
            count += 1;
        }
    }
    count
}

/// Asserts the evaluator's brute-force accept count equals the solver's SB-0
/// enumeration count for command `idx` of `src` (forbid overflow, the default).
fn assert_differential(src: &str) {
    assert_differential_opts(src, &SolveOptions::default());
}

/// The differential in **both** overflow modes — the mt-044 arithmetic net: the
/// encoder's polarity-threaded guard and the evaluator's must agree on the exact
/// accept-count whether overflow wraps (allow) or excludes (forbid).
fn assert_differential_both_modes(src: &str) {
    assert_differential_opts(src, &SolveOptions::default()); // forbid (default)
    assert_differential_opts(
        src,
        &SolveOptions {
            allow_overflow: true,
            ..SolveOptions::default()
        },
    );
}

fn assert_differential_opts(src: &str, opts: &SolveOptions) {
    let (ir, scoped, goal, bounds, layout) = build(src, 0);
    let solver_count = enumerate(&ir, &scoped, &goal, &bounds, opts)
        .expect("enumerate")
        .count();
    let eval_count = evaluator_count(&ir, &scoped, &goal, &layout, opts);
    assert_eq!(
        eval_count, solver_count,
        "encoder↔evaluator count mismatch for:\n{src}\n  evaluator={eval_count} solver={solver_count} (floating={}, allow_overflow={})",
        layout.total_floating, opts.allow_overflow
    );
}

#[test]
fn some_quantifier() {
    assert_differential("sig A {}\nrun { some A } for 3\n");
}

#[test]
fn all_quantifier_over_field() {
    assert_differential("sig A { r: set A }\nrun { all a: A | some a.r } for 2\n");
}

#[test]
fn no_one_lone_multiplicity_tests() {
    assert_differential("sig A {}\nrun { lone A } for 3\n");
    assert_differential("sig A {}\nrun { one A } for 3\n");
    assert_differential("sig A {}\nrun { no A } for 3\n");
}

#[test]
fn one_quantifier() {
    assert_differential("sig A { r: set A }\nrun { one a: A | no a.r } for 2\n");
}

#[test]
fn acyclicity_closure() {
    assert_differential("sig N { nx: set N }\nrun { no n: N | n in n.^nx } for 3\n");
}

#[test]
fn reflexive_closure() {
    assert_differential("sig N { nx: set N }\nrun { some n: N | N in n.*nx } for 2\n");
}

#[test]
fn subset_sigs() {
    assert_differential(
        "sig A {}\nsig B in A {}\nsig C in A {}\nrun { some B and no (B & C) } for 3\n",
    );
}

#[test]
fn field_one_multiplicity() {
    assert_differential("sig B {}\nsig A { f: one B }\nrun { some A } for 2\n");
}

#[test]
fn field_lone_multiplicity() {
    assert_differential("sig B {}\nsig A { f: lone B }\nrun { some f } for 2\n");
}

#[test]
fn cardinality_and_int_compare() {
    assert_differential("sig A {}\nsig B {}\nrun { #A = #B } for 2\n");
    assert_differential("sig A {}\nrun { #A = 2 } for 3\n");
}

#[test]
fn override_op() {
    assert_differential("sig K {}\nsig V {}\nsig M { m: K -> lone V }\nrun { some x: M | some (x.m ++ x.m) } for 2\n");
}

#[test]
fn domain_range_restrict() {
    assert_differential("sig A { r: set A }\nrun { some (A <: r) and some (r :> A) } for 2\n");
}

#[test]
fn transpose() {
    assert_differential("sig N { r: set N }\nrun { some n: N | some (n.~r) } for 2\n");
}

#[test]
fn comprehension() {
    assert_differential("sig A { r: set A }\nrun { some { a: A | some a.r } } for 2\n");
}

#[test]
fn union_intersect_diff() {
    assert_differential("sig A {}\nsig B in A {}\nsig C in A {}\nrun { some (B + C) and some (B & C) and some (A - B) } for 3\n");
}

// ================= arithmetic ops (mt-044), both overflow modes =============
// Small bitwidth (`2 int` = range −2..1) keeps `2^k` brute force cheap while
// still crossing the wrap boundary, so the forbid-mode guard actually fires.

// `<` is always an integer comparison (both sides lower via `int[·]`), so these
// exercise the arithmetic + overflow guard without hitting the §10.7c GAP1a
// relational-equality defer (which `arith = plain-Int-field` would trigger).
#[test]
fn arith_add_sub_mul_both_modes() {
    assert_differential_both_modes(
        "one sig X { v: one Int, w: one Int }\nrun { plus[X.v, X.w] < X.v } for 1 but 2 int\n",
    );
    assert_differential_both_modes(
        "one sig X { v: one Int, w: one Int }\nrun { minus[X.v, X.w] < X.w } for 1 but 2 int\n",
    );
    assert_differential_both_modes(
        "one sig X { v: one Int, w: one Int }\nrun { mul[X.v, X.w] < X.v } for 1 but 2 int\n",
    );
}

#[test]
fn arith_div_rem_both_modes() {
    // Includes div/rem by zero (v ranges over −2..1, so 0 is a possible divisor).
    assert_differential_both_modes(
        "one sig X { v: one Int, w: one Int }\nrun { div[X.v, X.w] < X.v } for 1 but 2 int\n",
    );
    assert_differential_both_modes(
        "one sig X { v: one Int, w: one Int }\nrun { rem[X.v, X.w] < X.w } for 1 but 2 int\n",
    );
}

#[test]
fn arith_negate_and_shift_both_modes() {
    assert_differential_both_modes(
        "one sig X { v: one Int }\nrun { negate[X.v] < X.v } for 1 but 2 int\n",
    );
    assert_differential_both_modes(
        "one sig X { v: one Int, w: one Int }\nrun { (X.v << X.w) < X.v } for 1 but 2 int\n",
    );
}

#[test]
fn arith_under_quantifiers_both_modes() {
    // A sig-bound `∀` overflow-driver (§10.7c rule 0: classified existential →
    // exclude, never rescued) and a sig-bound `∃`, both with `<` (an int
    // comparison), differentially checked so the encoder and evaluator agree on
    // the exclusion.
    assert_differential_both_modes(
        "sig A { v: one Int }\nrun { all a: A | plus[a.v, a.v] < a.v } for 2 but 2 int\n",
    );
    assert_differential_both_modes(
        "sig A { v: one Int }\nrun { some a: A | plus[a.v, a.v] < a.v } for 2 but 2 int\n",
    );
    // A bare-`Int` `∀` overflow-driver IS rescued — the differential pins the
    // rescue branch against the evaluator.
    assert_differential_both_modes("run { all n: Int | plus[n, n] < n } for 1 but 2 int\n");
}

#[test]
fn sum_and_int_ite_both_modes() {
    assert_differential_both_modes(
        "sig A { v: one Int }\nrun { (sum a: A | a.v) = 0 } for 2 but 2 int\n",
    );
    assert_differential_both_modes(
        "one sig X { v: one Int }\nrun { (X.v > 0 => plus[X.v, X.v] else X.v) < X.v } for 1 but 2 int\n",
    );
}

#[test]
fn eq_typing_defer_matches_between_encoder_and_evaluator() {
    // §10.7c GAP1a: `plus[X.v,7] = X.v` (arithmetic `Int[·]` vs a plain Int
    // field) typed-defers in FORBID mode. The matched-pair invariant requires the
    // encoder and evaluator to defer on *exactly* the same commands, so assert
    // both raise the defer in forbid and both succeed in allow.
    let src = "one sig X { v: one Int }\nrun { plus[X.v, 7] = X.v } for 1\n";
    let (ir, scoped, goal, bounds, layout) = build(src, 0);

    let forbid = SolveOptions::default();
    let allow = SolveOptions {
        allow_overflow: true,
        ..SolveOptions::default()
    };

    // Encoder defers in forbid, succeeds in allow.
    assert!(
        enumerate(&ir, &scoped, &goal, &bounds, &forbid).is_err(),
        "encoder must defer in forbid mode"
    );
    assert!(
        enumerate(&ir, &scoped, &goal, &bounds, &allow).is_ok(),
        "encoder must solve in allow mode"
    );

    // Evaluator defers identically on a concrete instance.
    let inst = instance_for(&layout, 0);
    let mut ev_forbid =
        Evaluator::new(&ir, &inst, &scoped, &forbid, goal.int_sig, goal.seq_int_sig);
    assert!(
        ev_forbid.accepts(goal.goal).is_err(),
        "evaluator must defer in forbid mode"
    );
    let mut ev_allow = Evaluator::new(&ir, &inst, &scoped, &allow, goal.int_sig, goal.seq_int_sig);
    assert!(
        ev_allow.accepts(goal.goal).is_ok(),
        "evaluator must accept/reject (not defer) in allow mode"
    );
}

#[test]
fn mixed_type_bare_int_nesting_differential() {
    // ∀∃ over bare `Int` (Defect B retracted, §10.7c): the per-variable rule now
    // solves this in both modes; the differential pins encoder ≡ evaluator on the
    // lifted classification. No floating vars (all over `Int`), so this is a
    // 0/1-instance agreement check.
    assert_differential_both_modes("run { all n: Int | some m: Int | plus[m, 7] < n }\n");
    assert_differential_both_modes("run { some n: Int | all m: Int | plus[m, 7] < n }\n");
}

#[test]
fn shl_junk_bit_overflow_differential() {
    // A bw4 left shift whose amount ranges over all 16 int values exercises the
    // masked-away junk-bit overflow (e.g. amount 4 = bit 2 set): the spurious
    // flag must reproduce identically in the evaluator, both overflow modes.
    assert_differential_both_modes(
        "one sig X { w: one Int }\nrun { (5 << X.w) < 0 } for 1 but 4 int\n",
    );
}

#[test]
fn int_next_prev_builtins() {
    // `util/integer` next/prev over the `Int/next` relation, differentially
    // checked against the evaluator.
    assert_differential("one sig X { v: one Int }\nrun { X.v.next = X.v } for 1 but 3 int\n");
    assert_differential("one sig X { v: one Int }\nrun { some X.v.prev } for 1 but 3 int\n");
}
