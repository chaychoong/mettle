//! Temporal IR/bounds conformance (mt-065): the static/variable relation
//! partition at every allocation site, the pinned temporal/static command
//! discriminator, and the k-state unroller over real, pipeline-built bounds.
//!
//! Jar-free: every expectation is a constant citing the pinned contract row it
//! comes from (`docs/reference/alloy6-temporal.md` §(a)/§(d)) or the reference
//! source line the rule is read off (`BoundsComputer.java`, `CompUtil.java`,
//! `CompModule.java` — cited by line, never copied), so CI runs it with no
//! oracle. Same shape as `int_conformance.rs`: tiny `MapLoader`-built models
//! driven through the real pipeline.
//!
//! Nothing here exercises solving: mt-065 lands machinery only, and neither
//! the discriminator nor the unroller is wired into lower/solve dispatch.

use als_core::ir::Ir;
use als_core::temporal::unroll;
use als_core::{compute_bounds, compute_universe};
use als_types::{is_temporal_model, resolve, MapLoader, ModuleGraph, ResolvedWorld};

// ------------------------------- harness ------------------------------------

/// Resolves `files` (first entry is the root) and returns the world plus graph.
fn load(files: &[(&str, &str)]) -> (ResolvedWorld, ModuleGraph) {
    let mut loader = MapLoader::new();
    for (path, src) in files {
        loader = loader.with(path, src);
    }
    let graph = ModuleGraph::load(files[0].0, &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    (world, graph)
}

/// Every relation `compute_bounds` allocates for command 0 of `src`, as
/// `(name, is_var)` in `RelId` (allocation) order.
fn partition(src: &str) -> Vec<(String, bool)> {
    let (world, graph) = load(&[("root.als", src)]);
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let _ = compute_bounds(&world, &scoped, &mut ir);
    ir.relations
        .iter()
        .map(|(_, r)| (r.name.clone(), r.is_var()))
        .collect()
}

/// The `is_var` flag of the relation named `name` in command 0 of `src`.
fn flag_of(src: &str, name: &str) -> bool {
    let table = partition(src);
    let hit: Vec<&(String, bool)> = table.iter().filter(|(n, _)| n == name).collect();
    assert_eq!(hit.len(), 1, "expected exactly one `{name}` in {table:?}");
    hit[0].1
}

/// The discriminator's verdict on command `index` of a single-file model.
fn is_temporal(src: &str, index: usize) -> bool {
    let (world, graph) = load(&[("root.als", src)]);
    is_temporal_model(&world, &graph, &world.commands[index])
}

/// The discriminator's verdict on command 0 of a multi-file model.
fn is_temporal_multi(files: &[(&str, &str)]) -> bool {
    let (world, graph) = load(files);
    is_temporal_model(&world, &graph, &world.commands[0])
}

// ==================== (1) the static/variable partition =====================
// Every rule below is read off `BoundsComputer`'s own `addRel(..., isVariable
// != null)` argument, so the partition is source-pinned per allocation shape,
// not inferred.

#[test]
fn leaf_sig_relation_follows_its_own_var_marker() {
    // BoundsComputer.java:178 — `sol.addRel(sig.label, lower, upper,
    // sig.isVariable != null)` for a childless prim sig.
    assert!(flag_of("var sig A {}\nrun {}\n", "this/A"));
    assert!(!flag_of("sig A {}\nrun {}\n", "this/A"));
}

#[test]
fn remainder_relation_follows_the_parent_not_the_children() {
    // BoundsComputer.java:194 — the `_remainder` relation is allocated with the
    // **parent sig's own** flag. A static parent with a `var` child keeps a
    // *static* remainder (the union is pinned rigid by its own `always (sum' =
    // sum)` formula at :206-207 instead, mt-066's business).
    assert!(flag_of(
        "var sig A {}\nsig B extends A {}\nrun {}\n",
        "this/A_remainder"
    ));
    assert!(!flag_of(
        "sig A {}\nvar sig B extends A {}\nrun {}\n",
        "this/A_remainder"
    ));
    // The child relation itself is a leaf and follows its own marker.
    assert!(flag_of(
        "sig A {}\nvar sig B extends A {}\nrun {}\n",
        "this/B"
    ));
    assert!(!flag_of(
        "var sig A {}\nsig B extends A {}\nrun {}\n",
        "this/B"
    ));
}

#[test]
fn subset_sig_relation_follows_its_own_var_marker() {
    // BoundsComputer.java:241 — `sol.addRel(sig.label, null, ts,
    // sig.isVariable != null)` for an `in` subset sig.
    assert!(flag_of("sig A {}\nvar sig B in A {}\nrun {}\n", "this/B"));
    assert!(!flag_of("sig A {}\nsig B in A {}\nrun {}\n", "this/B"));
}

#[test]
fn field_relation_follows_the_field_not_the_owner() {
    // BoundsComputer.java:448 — `sol.addRel(s.label + "." + f.label, null, ub,
    // f.isVariable != null)`: a static field of a `var` sig stays static, and a
    // `var` field of a static sig is variable.
    assert!(flag_of("sig A { var f: set A }\nrun {}\n", "this/A.f"));
    assert!(!flag_of("var sig A { f: set A }\nrun {}\n", "this/A.f"));
    assert!(flag_of("var sig A { f: set A }\nrun {}\n", "this/A"));
}

#[test]
fn var_one_sig_and_its_field_are_partitioned_independently() {
    // A `var one` sig keeps its own relation (the owner-column stripping in
    // `is_one_sig` already excludes var one-sigs), and its field follows the
    // field's marker as everywhere else.
    assert!(flag_of("var one sig A {}\nrun {}\n", "this/A"));
    assert!(flag_of("one sig A { var f: set A }\nrun {}\n", "this/A.f"));
    assert!(!flag_of("one sig A { var f: set A }\nrun {}\n", "this/A"));
}

#[test]
fn builtins_and_string_literals_are_always_static() {
    // alloy6-temporal.md §(d): `Int`/`seq/Int`/`String`/`seq` are never
    // `var`-declared, so integers and strings are rigid across states by
    // construction (probe T-13 saw them byte-identical in every state).
    let table = partition("var sig A { var f: set A }\nrun { some s: String | s = \"x\" }\n");
    for name in ["Int", "seq/Int", "String", "Int/next", "Int/zero", "\"x\""] {
        let hit = table.iter().find(|(n, _)| n == name);
        assert_eq!(hit.map(|(_, v)| *v), Some(false), "{name} must be static");
    }
}

#[test]
fn ordering_pinned_relations_are_static() {
    // `util/ordering`'s `Ord`/`First`/`Next` carry no `var` marker, so mt-035's
    // exact-bound pinning always lands on static relations
    // (BoundsComputer.java:417-418 passes the field's own flag).
    let src = "open util/ordering[A]\nsig A {}\nrun {}\n";
    for name in ["ordering/Ord", "ordering/Ord.First", "ordering/Ord.Next"] {
        assert!(!flag_of(src, name), "{name} must be static");
    }
}

#[test]
fn a_fully_static_model_has_no_variable_relation() {
    // Negative space (STYLE I1): the marker must stay off for every relation of
    // an ordinary Rung-3 model — this is what keeps mt-065 inert.
    let table = partition(
        "sig A { f: set B }\nsig B extends A {}\nsig C in A {}\none sig D {}\nrun { some A }\n",
    );
    assert!(!table.is_empty());
    assert!(
        table.iter().all(|(_, v)| !v),
        "static model grew a variable relation: {table:?}"
    );
}

// ======================== (2) the pinned discriminator ======================
// `CompUtil.isTemporalModel(sigs, cmd)` (CompUtil.java:189-201), alloy6-
// temporal.md §(a): temporal iff a `var` sig/field exists in the reachable
// world, **or** a temporal operator occurs in `globalFacts and commandBody`.

#[test]
fn a_var_sig_alone_is_temporal() {
    // Probe T-01: `var sig A {}; fact { some A }; run {}` → true, with zero
    // temporal operators anywhere.
    assert!(is_temporal("var sig A {}\nfact { some A }\nrun {}\n", 0));
}

#[test]
fn a_var_field_alone_is_temporal() {
    assert!(is_temporal("sig A { var f: set A }\nrun {}\n", 0));
}

#[test]
fn a_temporal_operator_alone_is_temporal() {
    // Probe T-02: `sig A {}; fact { always some A }; run {}` → true, with zero
    // `var` anywhere — the discriminator is a genuine `or`.
    assert!(is_temporal("sig A {}\nfact { always some A }\nrun {}\n", 0));
}

#[test]
fn neither_is_static() {
    // Probe T-03.
    assert!(!is_temporal("sig A {}\nfact { some A }\nrun {}\n", 0));
}

#[test]
fn every_temporal_operator_triggers_the_discriminator() {
    // The pinned 11: `Expr$2`'s two `visit` overrides match exactly AFTER,
    // BEFORE, PRIME, HISTORICALLY, ALWAYS, ONCE, EVENTUALLY / UNTIL, SINCE,
    // TRIGGERED, RELEASES (jar bytecode, alloy6-temporal.md §(a)).
    for body in [
        "always some A",
        "eventually some A",
        "after some A",
        "before some A",
        "historically some A",
        "once some A",
        "some A'",
        "some A until some A",
        "some A releases some A",
        "some A since some A",
        "some A triggered some A",
    ] {
        let src = format!("sig A {{}}\nrun {{ {body} }}\n");
        assert!(is_temporal(&src, 0), "`{body}` must be temporal");
    }
    // Negative space: the non-temporal unary/binary operators must not trip it.
    for body in ["some ~f", "some ^f", "some *f", "#A = 1", "some A + A"] {
        let src = format!("sig A {{ f: set A }}\nrun {{ {body} }}\n");
        assert!(!is_temporal(&src, 0), "`{body}` must stay static");
    }
}

#[test]
fn a_var_sig_in_an_opened_module_makes_every_command_temporal() {
    // The `var` half of the rule is **whole-world**, not command-reachable:
    // `CompUtil.isTemporalModel`'s `sigs` argument is the caller's complete
    // reachable-sig list (TranslateAlloyToKodkod.java:153 — "must be a complete
    // list"), so a `var` sig in an opened module counts even though the root
    // model never mentions it.
    assert!(is_temporal_multi(&[
        ("root.als", "open m\nsig A {}\nrun { some A }\n"),
        ("m.als", "module m\nvar sig B {}\n"),
    ]));
    // Same shape without the `var` marker stays static.
    assert!(!is_temporal_multi(&[
        ("root.als", "open m\nsig A {}\nrun { some A }\n"),
        ("m.als", "module m\nsig B {}\n"),
    ]));
}

#[test]
fn a_temporal_fact_in_an_opened_module_counts() {
    // `globalFacts` is `getAllReachableFacts()` — every free `fact` body of
    // every reachable module (CompModule.java:1905-1913).
    assert!(is_temporal_multi(&[
        ("root.als", "open m\nsig A {}\nrun { some A }\n"),
        ("m.als", "module m\nsig B {}\nfact { always some B }\n"),
    ]));
}

#[test]
fn the_operator_half_is_per_command() {
    // `cmd.formula` is `globalFacts.and(commandBody)` (CompModule.java:2030),
    // so a temporal operator in *another* command's body does not make this
    // command temporal.
    let src = "sig A {}\nrun { always some A }\nrun { some A }\n";
    assert!(is_temporal(src, 0));
    assert!(!is_temporal(src, 1));
}

#[test]
fn a_named_pred_or_assert_target_contributes_its_body() {
    // CompModule.java:1975-2014: `run p` substitutes `f.getBody()` directly and
    // `check a` substitutes the negated assertion body — both are part of
    // `cmd.formula`, so an operator written inside them counts.
    assert!(is_temporal(
        "sig A {}\npred p { always some A }\nrun p\n",
        0
    ));
    assert!(is_temporal(
        "sig A {}\nassert a { always some A }\ncheck a\n",
        0
    ));
    assert!(is_temporal(
        "sig A {}\npred p[x: A] { always some x }\nrun p\n",
        0
    ));
}

#[test]
fn the_scan_does_not_descend_into_a_called_pred_body() {
    // `Expr.hasTemporal()`'s query is a `VisitQuery`, and
    // `VisitQuery.visit(ExprCall)` iterates the call's `args` only — it never
    // enters `x.fun.getBody()` (jar bytecode,
    // `edu/mit/csail/sdg/ast/VisitQuery.class`). So an operator that lives only
    // inside a pred the command *calls* (rather than names) is invisible to the
    // discriminator. **Live-probe confirmed (mt-069, K1):** `isTemporalModel =
    // false`, plus a second confirmation via T-03's static-model `ErrorSyntax`
    // on a `steps`-scoped variant of the same command
    // (`scratchpad/probe/mt069/NOTES.md`).
    assert!(!is_temporal(
        "sig A {}\npred q { always some A }\npred p { q }\nrun p\n",
        0
    ));
    // ...but an operator in a call *argument* is visited.
    assert!(is_temporal(
        "sig A { f: set A }\npred q[x: A] { some x }\nrun { q[A'] }\n",
        0
    ));
}

#[test]
fn a_sig_appended_fact_is_outside_the_scanned_formula() {
    // `getAllReachableFacts()` collects free `fact` paragraphs only; a sig's
    // appended fact goes to `Sig.addFact` (CompModule.java:1884) and never
    // enters `globalFacts`. **Live-probe confirmed (mt-069, K2):**
    // `isTemporalModel = false` (`scratchpad/probe/mt069/NOTES.md`).
    assert!(!is_temporal("sig A {} { always some A }\nrun {}\n", 0));
}

#[test]
fn sequential_composition_counts_as_temporal() {
    // `;` is not a member of `ExprBinary$Op` at all: the jar desugars `a ; b`
    // to `a and after b` before resolution, so the tree `hasTemporal()` scans
    // holds an `AFTER`. **Live-probe confirmed (mt-069, K3):** `isTemporalModel
    // = true`, and a `steps` scope on the same command solves cleanly (no
    // `ErrorSyntax`) — the positive-side confirmation K1/K2 lacked
    // (`scratchpad/probe/mt069/NOTES.md`).
    assert!(is_temporal("sig A {}\nrun { some A ; some A }\n", 0));
}

// ============================ (3) the unroller ==============================

/// Builds command 0's bounds and unrolls them to `k`.
fn unrolled_shape(src: &str, k: usize) -> (Vec<(String, bool)>, usize, usize) {
    let (world, graph) = load(&[("root.als", src)]);
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let built = compute_bounds(&world, &scoped, &mut ir);
    let before = built.bounds.iter().count();
    let view = unroll(&mut ir, &built.bounds, k);
    let after = view.bounds.iter().count();
    let names = view
        .bounds
        .iter()
        .map(|(r, _)| (ir.relations[r].name.clone(), ir.relations[r].is_var()))
        .collect();
    (names, before, after)
}

#[test]
fn unrolling_pipeline_bounds_copies_exactly_the_var_relations() {
    let src = "var sig A { var f: set A }\nsig B {}\nrun {}\n";
    let (names, before, after) = unrolled_shape(src, 3);
    // 2 variable relations (`this/A`, `this/A.f`) become 3 copies each.
    assert_eq!(after, before + 2 * (3 - 1));
    let copies: Vec<&String> = names
        .iter()
        .filter(|(_, v)| *v)
        .map(|(n, _)| n)
        .collect::<Vec<_>>();
    assert_eq!(
        copies,
        vec![
            "this/A@0",
            "this/A@1",
            "this/A@2",
            "this/A.f@0",
            "this/A.f@1",
            "this/A.f@2",
        ]
    );
    // Every static relation of the original survives untouched.
    assert!(names.iter().any(|(n, v)| n == "this/B" && !v));
    assert!(names.iter().any(|(n, v)| n == "Int" && !v));
}

#[test]
fn unrolling_a_static_model_is_the_identity_at_every_k() {
    let src = "sig A { f: set A }\nsig B extends A {}\nrun {}\n";
    for k in 1..4 {
        let (_, before, after) = unrolled_shape(src, k);
        assert_eq!(before, after, "static bounds must not grow at k={k}");
    }
}

#[test]
fn unrolling_pipeline_bounds_is_deterministic() {
    // STYLE U4: build twice from scratch and compare the whole unrolled view.
    let src = "var sig A { var f: set A }\nsig B in A {}\nrun {}\n";
    assert_eq!(unrolled_shape(src, 4), unrolled_shape(src, 4));
}

#[test]
fn the_bridge_map_is_total_over_the_var_relations() {
    let (world, graph) = load(&[("root.als", "var sig A { var f: set A }\nrun {}\n")]);
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let built = compute_bounds(&world, &scoped, &mut ir);
    let originals: Vec<_> = built
        .bounds
        .iter()
        .filter(|(r, _)| ir.relations[*r].is_var())
        .map(|(r, _)| r)
        .collect();
    let view = unroll(&mut ir, &built.bounds, 2);
    assert_eq!(view.states.len(), originals.len());
    for original in originals {
        assert!(view.is_unrolled(original));
        for state in 0..view.k {
            let copy = view.at(original, state).expect("copy");
            assert_eq!(view.bounds.get(copy), built.bounds.get(original));
        }
        // The original is replaced outright, never left bound alongside.
        assert!(view.bounds.get(original).is_none());
    }
}
