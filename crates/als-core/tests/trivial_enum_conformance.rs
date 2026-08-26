//! Trivially-true-goal enumeration conformance (mt-136, translation-ref §16.5).
//! Jar-free and CI-safe: every pinned count was produced by running the
//! reference jar (`oracle/org.alloytools.alloy.dist.jar`) **at authoring time**
//! on the model quoted in each test, via the mt-107 `CountProbe` runner
//! (`scratchpad/probe/mt107/run.sh count <cell>.als all <sym> 100000`, sat4j,
//! `noOverflow=true`, each invocation under a hard `timeout`). The reconciled
//! table and the jar dumps behind it are in `scratchpad/probe/mt136/NOTES.md`;
//! the models are cached one-per-file in `scratchpad/probe/mt136/cells/`.
//!
//! Every model here is `run {}` — a body that translates to the boolean constant
//! TRUE — over bounds that leave something free. The reference does **not**
//! enumerate that case by iterating one translation: `ExtendedSolver`'s
//! `SolutionIterator.nextTrivialSolution` (`:212-260`) answers with the trivial
//! instance (every relation at its lower bound) and then re-translates the
//! *residual* problem — "differ from that instance" — from scratch, detecting a
//! fresh, **coarser** partition (no int/string singletons, no exact relation to
//! refine on) and applying a real lex-leader SBP over it. So a constant circuit
//! is quotiented after all, just by a different plan than the goal's own.
//!
//! Both symmetries are asserted per cell. SB-0 pins the raw model count, which
//! the trivial-first restructure must leave alone (it only rearranges *which*
//! instance comes first and how the rest are excluded); SB-20 pins the residual
//! quotient, which is what mt-136 fixed.

use als_core::ir::Ir;
use als_core::{compute_bounds, compute_universe, enumerate, lower_command, SolveOptions};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Exhaustively enumerates command 0 of `src` at the given symmetry cap and
/// returns the count. `symmetry = 0` disables SBP (the raw SB-0 count); any
/// non-zero value is the lex-leader cap (translation-ref §16.3).
fn count_at(src: &str, symmetry: u32) -> usize {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    let opts = SolveOptions {
        symmetry,
        ..SolveOptions::default()
    };
    enumerate(&ir, &scoped, &goal, &bounds, &opts)
        .expect("enumerate")
        .count()
}

/// c1 — an ordered leaf sig pinned exactly, and nothing else. Every relation is
/// a constant, so the residual formula is the reference's `changes.isEmpty()`
/// case (`ExtendedSolver.java:254`): `FALSE`, i.e. the trivial instance is the
/// only one. **1 at both symmetries.**
#[test]
fn c1_leaf() {
    let src = "open util/ordering[S]\nsig S {}\nrun {} for exactly 3 S\n";
    assert_eq!(count_at(src, 0), 1, "c1 SB=0 = 1");
    assert_eq!(count_at(src, 20), 1, "c1 SB=20 = 1");
}

/// c2 — a non-exact child of an ordered sig. The scope constraint keeps the goal
/// circuit non-constant, so this is the ordinary §16.1 path; it rides along as a
/// control that the mt-136 restructure did not disturb it. **42 / 7.**
#[test]
fn c2_child_nonexact() {
    let src = "open util/ordering[S]\nsig S {}\nsig A extends S {}\nrun {} for 3 S, 2 A\n";
    assert_eq!(count_at(src, 0), 42, "c2 SB=0 = 42");
    assert_eq!(count_at(src, 20), 7, "c2 SB=20 = 7");
}

/// c3 — the child's exact scope fills its parent. **6 / 1.**
#[test]
fn c3_child_fills_exact() {
    let src = "open util/ordering[S]\nsig S {}\nsig A extends S {}\nrun {} for 3 S, exactly 3 A\n";
    assert_eq!(count_at(src, 0), 6, "c3 SB=0 = 6");
    assert_eq!(count_at(src, 20), 1, "c3 SB=20 = 1");
}

/// c4 — two exact children partitioning an exact ordered parent. **24 / 6.**
#[test]
fn c4_two_exact() {
    let src = "open util/ordering[S]\nsig S {}\nsig A extends S {}\nsig B extends S {}\nrun {} for exactly 4 S, exactly 2 A, exactly 2 B\n";
    assert_eq!(count_at(src, 0), 24, "c4 SB=0 = 24");
    assert_eq!(count_at(src, 20), 6, "c4 SB=20 = 6");
}

/// c5 — the sharp cell. `S` is ordered and pinned exactly-3, so the goal folds to
/// TRUE and the *first* translation's partition splits `S`'s atoms into
/// singletons (the pinned `Next` chain distinguishes them). The residual
/// translation does not see that chain at all — only `this/A`'s free bound — so
/// its partition puts the three `S` atoms back in one class and quotients `A`'s
/// 8 subsets to the 4 orbits of Sym(3) on a 3-element powerset. **8 / 4**; mettle
/// answered 8/8 before mt-136.
#[test]
fn c5_subset() {
    let src = "open util/ordering[S]\nsig S {}\nsig A in S {}\nrun {} for exactly 3 S\n";
    assert_eq!(count_at(src, 0), 8, "c5 SB=0 = 8");
    assert_eq!(count_at(src, 20), 4, "c5 SB=20 = 4");
}

/// c6 — an abstract ordered parent with two exact children. **24 / 6.**
#[test]
fn c6_abstract_two() {
    let src = "open util/ordering[S]\nabstract sig S {}\nsig A extends S {}\nsig B extends S {}\nrun {} for 4 S, exactly 2 A, exactly 2 B\n";
    assert_eq!(count_at(src, 0), 24, "c6 SB=0 = 24");
    assert_eq!(count_at(src, 20), 6, "c6 SB=20 = 6");
}

/// c7 — the ordering is on the *child*, leaving 0–2 non-`A` atoms of `S` free.
/// The residual sees only that remainder relation, and quotients its 4 raw
/// assignments to the 3 upward-closed orbits (∅, singleton, full) — the classic
/// Y1 shape. **4 / 3**; mettle answered 4/4 before mt-136.
#[test]
fn c7_child_ordered() {
    let src = "open util/ordering[A]\nsig S {}\nsig A extends S {}\nrun {} for 4 S, exactly 2 A\n";
    assert_eq!(count_at(src, 0), 4, "c7 SB=0 = 4");
    assert_eq!(count_at(src, 20), 3, "c7 SB=20 = 3");
}

/// c8 — a field on the ordered sig, so the goal circuit is non-constant (control
/// cell, as c2). **3072 / 1536.**
#[test]
fn c8_field() {
    let src = "open util/ordering[S]\nsig S { f: set S }\nsig A extends S {}\nsig B extends S {}\nrun {} for 3 S, exactly 1 A, exactly 2 B\n";
    assert_eq!(count_at(src, 0), 3072, "c8 SB=0 = 3072");
    assert_eq!(count_at(src, 20), 1536, "c8 SB=20 = 1536");
}

/// c9 — a `one` child of an ordered parent. **6 / 3.**
#[test]
fn c9_one_child() {
    let src = "open util/ordering[S]\nsig S {}\none sig A extends S {}\nrun {} for 3 S\n";
    assert_eq!(count_at(src, 0), 6, "c9 SB=0 = 6");
    assert_eq!(count_at(src, 20), 3, "c9 SB=20 = 3");
}

/// c10 — a non-exact child whose scope numerically equals its non-exact parent's,
/// the cell built to stress `breakTotalOrder`'s firing condition. Neither side
/// pins the order here, and the counts agree. **48 / 8.**
#[test]
fn c10_child_fills_nonexact() {
    let src = "open util/ordering[S]\nsig S {}\nsig A extends S {}\nrun {} for 3 S, 3 A\n";
    assert_eq!(count_at(src, 0), 48, "c10 SB=0 = 48");
    assert_eq!(count_at(src, 20), 8, "c10 SB=20 = 8");
}

/// c11 — the minimal reproduction, with no `util/ordering` anywhere: the
/// divergence is about the trivial-solution enumerator, not about ordering. Same
/// shape and same counts as c5. **8 / 4**; mettle answered 8/8 before mt-136.
#[test]
fn c11_vacuous_no_ordering() {
    let src = "sig S {}\nsig A in S {}\nrun {} for exactly 3 S\n";
    assert_eq!(count_at(src, 0), 8, "c11 SB=0 = 8");
    assert_eq!(count_at(src, 20), 4, "c11 SB=20 = 4");
}

/// The trivial instance is the enumeration's **first** answer and appears
/// **exactly once** (translation-ref §16.5, `ExtendedSolver.java:218`): the
/// residual excludes it, so the solve/block loop that follows can never produce
/// it again. Checked on c11 at both symmetries — the residual's SBP must not
/// change which instance comes first.
#[test]
fn the_trivial_instance_comes_first_and_only_once() {
    let src = "sig S {}\nsig A in S {}\nrun {} for exactly 3 S\n";
    for symmetry in [0, 20] {
        let loader = MapLoader::new().with("root.als", src);
        let graph = ModuleGraph::load("root.als", &loader).expect("load");
        let world = resolve(&graph).expect("resolve").world;
        let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
        let mut ir = Ir::default();
        let bounds = compute_bounds(&world, &scoped, &mut ir);
        let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
        let opts = SolveOptions {
            symmetry,
            ..SolveOptions::default()
        };
        let instances: Vec<_> = enumerate(&ir, &scoped, &goal, &bounds, &opts)
            .expect("enumerate")
            .collect();

        // Every relation at its lower bound — `this/A` empty, and nothing else
        // free — is what the first instance must be.
        let first = &instances[0];
        for (rel, bound) in bounds.bounds.iter() {
            assert_eq!(
                first.get(rel),
                Some(bound.lower()),
                "the first instance is not the trivial one at symmetry {symmetry}"
            );
        }
        assert_eq!(
            instances.iter().filter(|i| *i == first).count(),
            1,
            "the trivial instance was enumerated twice at symmetry {symmetry}"
        );
    }
}
