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
    let scoped = compute_universe(&world, &world.commands[idx]).expect("universe");
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
fn evaluator_count(ir: &Ir, scoped: &ScopedUniverse, goal: &LoweredGoal, layout: &Layout) -> usize {
    assert!(
        layout.total_floating <= 20,
        "brute force too wide: {} floating vars",
        layout.total_floating
    );
    let opts = SolveOptions::default();
    let mut count = 0usize;
    for mask in 0..(1u64 << layout.total_floating) {
        let inst = instance_for(layout, mask);
        let mut ev = Evaluator::new(ir, &inst, scoped, &opts);
        if ev.accepts(goal.goal).expect("evaluable goal") {
            count += 1;
        }
    }
    count
}

/// Asserts the evaluator's brute-force accept count equals the solver's SB-0
/// enumeration count for command `idx` of `src`.
fn assert_differential(src: &str) {
    let (ir, scoped, goal, bounds, layout) = build(src, 0);
    let solver_count = enumerate(&ir, &scoped, &goal, &bounds, &SolveOptions::default())
        .expect("enumerate")
        .count();
    let eval_count = evaluator_count(&ir, &scoped, &goal, &layout);
    assert_eq!(
        eval_count, solver_count,
        "encoder↔evaluator count mismatch for:\n{src}\n  evaluator={eval_count} solver={solver_count} (floating={})",
        layout.total_floating
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
