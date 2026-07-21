//! Self-check negative tests (mt-034, translation-ref §6): a *correct* solved
//! instance passes [`self_check`]; a hand-corrupted one (a tuple added or
//! removed) is **rejected**, and the failure is localized to the right top-level
//! conjunct via its [`Provenance`]. This exercises the net's teeth — the same
//! check `solve_goal` runs as a `debug_assert!` on every SAT verdict.

use als_core::bounds::{Bounds, Tuple, TupleSet};
use als_core::ir::{Ir, RelId};
use als_core::{
    compute_bounds, compute_universe, lower_command, self_check, solve_goal, Instance, Provenance,
    ScopedUniverse, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

struct Solved {
    ir: Ir,
    scoped: ScopedUniverse,
    goal: als_core::LoweredGoal,
    instance: Instance,
    bounds: Bounds,
}

fn solve(src: &str) -> Solved {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    let instance =
        match solve_goal(&ir, &scoped, &goal, &bounds, &SolveOptions::default()).expect("solve") {
            SolveVerdict::Sat(inst) => inst,
            SolveVerdict::Unsat => panic!("expected SAT for a corruption test:\n{src}"),
            // No budget set (default options), so `Unknown` is unreachable.
            SolveVerdict::Unknown => unreachable!("unbudgeted solve returned Unknown"),
        };
    Solved {
        ir,
        scoped,
        goal,
        instance,
        bounds: bounds.bounds,
    }
}

/// Rebuilds an instance with `rel`'s tuple set replaced.
fn with_rel(inst: &Instance, target: RelId, new: &TupleSet) -> Instance {
    let rels = inst
        .iter()
        .map(|(r, ts)| (r, if r == target { new.clone() } else { ts.clone() }));
    Instance::from_relations(inst.universe.clone(), rels.collect::<Vec<_>>())
}

/// Finds a relation by diagnostic name.
fn rel_named(ir: &Ir, name: &str) -> RelId {
    ir.relations
        .iter()
        .find(|(_, r)| r.name == name)
        .map_or_else(|| panic!("no relation named {name}"), |(id, _)| id)
}

#[test]
fn correct_instance_passes() {
    let s = solve("sig A {}\nfact NonEmpty { some A }\nrun {} for 3\n");
    assert!(self_check(
        &s.ir,
        &s.scoped,
        &s.goal,
        &s.instance,
        &SolveOptions::default(),
        &s.bounds,
    )
    .is_ok());
}

#[test]
fn corrupting_a_fact_is_caught() {
    // `fact NonEmpty { some A }` holds in the solved instance; empty out A and the
    // self-check must reject, blaming the Fact conjunct.
    let s = solve("sig A {}\nfact NonEmpty { some A }\nrun {} for 3\n");
    let a = rel_named(&s.ir, "A");
    let corrupt = with_rel(&s.instance, a, &TupleSet::empty(1));
    let failure = self_check(
        &s.ir,
        &s.scoped,
        &s.goal,
        &corrupt,
        &SolveOptions::default(),
        &s.bounds,
    )
    .expect_err("corrupted instance must be rejected");
    assert!(
        matches!(failure.provenance, Provenance::Fact),
        "expected a Fact failure, got {:?}",
        failure.provenance
    );
}

#[test]
fn corrupting_a_field_multiplicity_is_caught() {
    // `f: one B` forces exactly one `f` per `A`. Emptying `A.f` breaks the `one`
    // multiplicity → the FieldFact conjunct is blamed.
    let s = solve("sig B {}\nsig A { f: one B }\nrun { some A } for 2\n");
    let f = rel_named(&s.ir, "A.f");
    let corrupt = with_rel(&s.instance, f, &TupleSet::empty(2));
    let failure = self_check(
        &s.ir,
        &s.scoped,
        &s.goal,
        &corrupt,
        &SolveOptions::default(),
        &s.bounds,
    )
    .expect_err("emptying a `one` field must be rejected");
    assert!(
        matches!(failure.provenance, Provenance::FieldFact(_)),
        "expected a FieldFact failure, got {:?}",
        failure.provenance
    );
}

#[test]
fn corrupting_the_command_is_caught() {
    // The command `some A` holds; empty A and the Command conjunct is blamed
    // (facts/fields above it still pass).
    let s = solve("sig A {}\nrun { some A } for 3\n");
    let a = rel_named(&s.ir, "A");
    let corrupt = with_rel(&s.instance, a, &TupleSet::empty(1));
    let failure = self_check(
        &s.ir,
        &s.scoped,
        &s.goal,
        &corrupt,
        &SolveOptions::default(),
        &s.bounds,
    )
    .expect_err("emptying A must violate `some A`");
    assert!(
        matches!(failure.provenance, Provenance::Command),
        "expected a Command failure, got {:?}",
        failure.provenance
    );
}

#[test]
fn adding_an_illegal_tuple_is_caught() {
    // `f: one B` — give some A a *second* legal image, breaking `one`.
    // Force at least two B atoms so a second, *type-legal* image exists.
    let s = solve("sig B {}\nsig A { f: one B }\nrun { some A and #B = 2 } for 2\n");
    let f = rel_named(&s.ir, "A.f");
    let b = rel_named(&s.ir, "B");
    let b_atoms: Vec<_> = s
        .instance
        .get(b)
        .expect("B decoded")
        .iter()
        .map(|t| t.atoms()[0])
        .collect();
    assert!(b_atoms.len() >= 2, "need two B atoms to over-fill `one`");
    let existing = s
        .instance
        .get(f)
        .and_then(|ts| ts.iter().next().cloned())
        .expect("some A has an f image");
    let a0 = existing.atoms()[0];
    let b0 = existing.atoms()[1];
    let other_b = *b_atoms.iter().find(|&&x| x != b0).expect("a second B atom");
    let mut fat = s.instance.get(f).expect("f decoded").clone();
    fat.insert(Tuple::new(vec![a0, other_b])); // a0 now maps to two B atoms

    let corrupt = with_rel(&s.instance, f, &fat);
    let failure = self_check(
        &s.ir,
        &s.scoped,
        &s.goal,
        &corrupt,
        &SolveOptions::default(),
        &s.bounds,
    )
    .expect_err("a second f image must break `one`");
    assert!(
        matches!(failure.provenance, Provenance::FieldFact(_)),
        "expected a FieldFact failure, got {:?}",
        failure.provenance
    );
}
