//! First-order skolemization conformance (mt-047, translation-ref §15 + probes
//! §10.11 K1–K4). Jar-free and CI-safe: every constant cites its jar-pinned
//! probe row; the tests never run the jar (STYLE U3).
//!
//! At `skolemDepth 0` a top-level effective-existential first-order decl — `some
//! x: e | φ` at positive polarity, or the `all` of a `check`'s negated body, not
//! nested under any effective-universal — lowers to a fresh **skolem constant
//! relation** `$<cmdLabel>_<var>` (bare `$<var>` for an anonymous command) with a
//! `one` + membership constraint, instead of a quantifier. This makes SB-0
//! enumeration count each witness (K4) and shows the witness in the instance
//! (K1/K2), never changing the verdict.

use als_core::ir::{Ir, RelId};
use als_core::{
    compute_bounds, compute_universe, enumerate, lower_command, solve_goal, Instance, SolveOptions,
    SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Runs the whole pipeline for command 0 of `src`, expecting SAT, and returns the
/// decoded instance plus the `Ir` (for relation-name lookups).
fn sat_instance(src: &str) -> (Instance, Ir) {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    let verdict =
        solve_goal(&ir, &scoped, &goal, &bounds, &SolveOptions::default()).expect("solve");
    match verdict {
        SolveVerdict::Sat(inst) => (inst, ir),
        other => panic!("expected SAT, got {other:?}:\n{src}"),
    }
}

/// The SB-0 enumeration count of command 0 of `src`.
fn count(src: &str) -> usize {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    // SB-0 counting yardstick (ADR-0002): symmetry off, so these pinned counts are
    // the raw jar SB-0 counts (K4 = 12, NoEmpty = 561). `SolveOptions::default()`
    // now defaults symmetry to 20 (mt-048), a different quotiented count.
    let opts = SolveOptions {
        symmetry: 0,
        ..SolveOptions::default()
    };
    enumerate(&ir, &scoped, &goal, &bounds, &opts)
        .expect("enumerate")
        .count()
}

/// The `RelId` of the relation named `name`, if any.
fn rel_named(ir: &Ir, name: &str) -> Option<RelId> {
    ir.relations
        .iter()
        .find(|(_, r)| r.name == name)
        .map(|(id, _)| id)
}

/// Every relation name in the instance beginning with `$` (the skolem sigil).
fn skolem_names(inst: &Instance, ir: &Ir) -> Vec<String> {
    inst.iter()
        .map(|(rel, _)| ir.relations[rel].name.clone())
        .filter(|n| n.starts_with('$'))
        .collect()
}

/// Asserts the instance carries a skolem relation `name` that is a **singleton**
/// (arity 1, exactly one tuple) whose atom is a member of the sig relation
/// `sig_name` — the `one $var` + `$var in Sig` decl constraint made concrete.
fn assert_singleton_in_sig(inst: &Instance, ir: &Ir, name: &str, sig_name: &str) {
    let skolem = rel_named(ir, name)
        .and_then(|r| inst.get(r))
        .unwrap_or_else(|| {
            panic!(
                "no skolem relation `{name}`; skolems={:?}",
                skolem_names(inst, ir)
            )
        });
    assert_eq!(skolem.arity(), 1, "`{name}` must be unary");
    assert_eq!(skolem.len(), 1, "`{name}` must be a singleton (`one`)");
    let sig = rel_named(ir, sig_name)
        .and_then(|r| inst.get(r))
        .unwrap_or_else(|| panic!("no sig relation `{sig_name}`"));
    let tuple = skolem.iter().next().expect("singleton has one tuple");
    assert!(
        sig.contains(tuple),
        "`{name}` = {tuple:?} must be a member of `{sig_name}` = {sig:?}"
    );
}

// ------------------------------------------------------------------ K1 / K2

/// K1 (§10.11): a named command's top-level `some x: A` skolemizes to the
/// constant relation `$<cmdLabel>_<var>` = `$foo_x`, a singleton inside A.
#[test]
fn k1_named_command_skolem_is_labelled() {
    let (inst, ir) = sat_instance("sig A {}\nrun foo { some x: A | x = x } for 3\n");
    assert_singleton_in_sig(&inst, &ir, "$foo_x", "this/A");
}

/// K2 (§10.11): an anonymous command's label contains `$` (jar `run$1`), so the
/// prefix is dropped and the skolem is the bare `$x`.
#[test]
fn k2_anonymous_command_skolem_is_bare() {
    let (inst, ir) = sat_instance("sig A {}\nrun { some x: A | x = x } for 3\n");
    assert_singleton_in_sig(&inst, &ir, "$x", "this/A");
}

// ------------------------------------------------------------------ K3

/// K3 (§10.11): an existential nested under a universal is NOT skolemized at
/// depth 0 (it would need a skolem function). The instance carries **no** `$`
/// skolem relation, and the verdict is unchanged (SAT).
#[test]
fn k3_existential_under_universal_is_not_skolemized() {
    let (inst, ir) = sat_instance("sig A {}\nrun bar { all y: A | some x: A | x != y } for 3\n");
    assert!(
        skolem_names(&inst, &ir).is_empty(),
        "no skolem expected under a universal; got {:?}",
        skolem_names(&inst, &ir)
    );
}

// ------------------------------------------------------------------ K4

/// K4 (§10.11): the SB-0 count of `run { some x: A | x=x } for 3` is **12** —
/// the jar (and now mettle) enumerates each skolem-constant witness
/// (`12 = Σ_{∅≠S⊆A} |S|`). Before FO skolemization mettle counted 7.
#[test]
fn k4_top_level_some_counts_each_witness() {
    assert_eq!(count("sig A {}\nrun { some x: A | x = x } for 3\n"), 12);
}

/// K4 control: a goal with **no** skolemizable quantifier is unchanged. `some A`
/// is a multiplicity *test* on the expression `A`, not a `some x: A` quantifier,
/// so nothing skolemizes and the count stays the jar's SB-0 **7** (§10.11 Y1 /
/// §3 T3: the 7 non-empty subsets of a 3-atom sig).
#[test]
fn k4_control_non_quantifier_shape_unchanged() {
    assert_eq!(count("sig A {}\nrun { some A } for 3\n"), 7);
}

// -------------------------------------------------------------- disj skolems

/// `some disj x, y: A | x != y`: each var skolemizes to its own singleton
/// relation, and the pre-colon `disj` keeps `no ($x & $y)` — so the two skolems
/// are distinct singletons. Verdict SAT (A needs ≥ 2 atoms; scope 3 allows it).
#[test]
fn disj_group_skolemizes_each_var_and_holds_disjointness() {
    let (inst, ir) = sat_instance("sig A {}\nrun { some disj x, y: A | x != y } for 3\n");
    assert_singleton_in_sig(&inst, &ir, "$x", "this/A");
    assert_singleton_in_sig(&inst, &ir, "$y", "this/A");
    let x = inst.get(rel_named(&ir, "$x").unwrap()).unwrap();
    let y = inst.get(rel_named(&ir, "$y").unwrap()).unwrap();
    let xt = x.iter().next().unwrap();
    let yt = y.iter().next().unwrap();
    assert!(
        !y.contains(xt) && !x.contains(yt),
        "disj skolems must be disjoint: $x={x:?} $y={y:?}"
    );
}

// ----------------------------------------------------------- check polarity

/// A `check` whose negated body is a top-level effective-existential: the `all`
/// sits at negative polarity, so it skolemizes (polarity flip) and is named from
/// the command label — `$NoEmpty_b`. This is `oracle/test1.als`'s `check NoEmpty`
/// (§10.4), SAT with the counterexample witness carried as the skolem singleton.
#[test]
fn check_negated_all_skolemizes_with_command_label() {
    let (inst, ir) = sat_instance(
        "sig A {}\nsig B { r: set A }\nassert NoEmpty { all b: B | some b.r }\ncheck NoEmpty for 3\n",
    );
    assert_singleton_in_sig(&inst, &ir, "$NoEmpty_b", "this/B");
}

/// The jar-pinned SB-0 count of `check NoEmpty` is **561** (§10.4/§15), matching
/// mettle once the negated `all` skolemizes (was 464 un-skolemized).
#[test]
fn check_noempty_count_matches_jar_561() {
    assert_eq!(
        count("sig A {}\nsig B { r: set A }\nassert NoEmpty { all b: B | some b.r }\ncheck NoEmpty for 3\n"),
        561
    );
}

// ----------------------------------------------------------- uniquification

/// Two same-shape existentials under one command both want the base name
/// `$foo_x`; the jar's `un.make` uniquifies (translation-ref §15). mettle mints
/// **two distinct relations with distinct names**, so both witnesses are counted
/// (the verdict/count depend only on the relations being distinct).
#[test]
fn colliding_skolem_names_are_uniquified() {
    let (inst, ir) =
        sat_instance("sig A {}\nrun foo { (some x: A | x = x) and (some x: A | x = x) } for 3\n");
    let mut names = skolem_names(&inst, &ir);
    names.sort();
    assert_eq!(
        names,
        vec!["$foo_x".to_owned(), "$foo_x_2".to_owned()],
        "two colliding `$foo_x` skolems must get distinct names"
    );
}

/// §15 naming: an existential inside an inlined *called* pred body takes the
/// innermost **function's** tail label, not the command's — `run foo { q }` with
/// `some x: A` inside `q` mints `$q_x` (tech-lead review probe, mt-047).
#[test]
fn called_pred_existential_uses_func_label() {
    let (inst, ir) = sat_instance("sig A {}\npred q { some x: A | x = x }\nrun foo { q } for 3\n");
    assert_singleton_in_sig(&inst, &ir, "$q_x", "this/A");
}

/// A decl bounded by an EARLIER skolem must still skolemize — its upper comes
/// from the lowerer's own `skolem_bounds`, which the bounds builder never saw
/// (mt-047 review fix; the addressBook2e[3] `all b: Book, n: b.names | …`
/// under-count). Both witnesses must appear as skolem relations.
#[test]
fn dependent_decl_skolemizes_through_earlier_skolem() {
    let (inst, ir) = sat_instance(
        "sig T {}\nsig B { names: set T }\nassert q { all b: B, n: b.names | n != n }\ncheck q for 3\n",
    );
    assert_singleton_in_sig(&inst, &ir, "$q_b", "this/B");
    assert_singleton_in_sig(&inst, &ir, "$q_n", "this/T");
}
