//! `$`-metamodel lowering conformance (mt-107 P3): jar-pinned verdicts for the
//! synthesized meta relations and for the phase-8 **ground expansion**.
//!
//! Every row cites its cell from the P0 probe wave
//! (`scratchpad/probe/mt107/NOTES.md`, verdicts in
//! `scratchpad/probe/mt107/out/VERDICTS.txt`), recorded against Alloy 6.2.0 so
//! CI runs with no oracle. Cells were SAT/UNSAT-identical under both
//! `A4Options.noOverflow` settings, so these run in the default (forbid) mode
//! only.
//!
//! Two things are under test, and they are independent:
//!
//! 1. **The defined meta relations.** `value` / `fields` / `parent` /
//!    `subfields` are synthesized *defined* fields whose value comes from
//!    [`als_types::MetaDef`], not from any source AST (see
//!    [`als_types::ResolvedField::bound`]) — M1 pins what each one denotes.
//! 2. **The ground expansion.** `all` / `some` / `{…}` over a `one`-of
//!    meta-typed bound is not a binder at all: the resolver replaced it with a
//!    fold of the body re-resolved once per meta atom, and lowering replays that
//!    fold — M2 pins the three folds, their empty cases, and the negative space
//!    (`no`/`one` are *not* expanded).
//!
//! 3. **The synthesis's emptiness facts.** `resolveMeta` adds `no <sig>` for
//!    each synthesized sig it left without members; the lowerer replays what P1
//!    recorded in `MetaModel::empty_facts` — M5 pins the reachable one
//!    (`var$fact`) and the variability partition that decides when it is minted.
//!
//! The scope-and-universe half of the feature (atom order, XML `meta="yes"`)
//! is mt-107 P4's and is deliberately not asserted here.
//!
//! The sig-less emptiness facts, stated as a gap at P3, were jar-probed at P5
//! (cells `p5/p5_01`–`p5_04`, 2026-08-25, both overflow modes): all three
//! facts mint on a model with no sigs (`sig$fact`, `static$fact`, `var$fact`
//! in the root-fact dump) and the verdicts are pinned in the `p5_*` tests
//! below.

use als_core::ir::Ir;
use als_core::{
    compute_bounds, compute_universe, lower_command, solve_goal, SolveOptions, SolveVerdict,
};
use als_types::{resolve, MapLoader, ModuleGraph};

/// The M1/M2 base model (`NOTES.md` §M1): three sigs, three fields, one
/// `extends` chain, so `sig$ = {V$, W$, Z$}` and `field$ = {V$f, V$g, W$h}`.
const BASE: &str = "abstract sig V { f: lone V, g: lone V }\n\
     sig W extends V { h: lone W }\n\
     sig Z {}\n";

/// Solves command 0 of `src` in the default (overflow-forbidding) mode.
/// `true` = SAT, `false` = UNSAT. Any defer or rejection panics: every cell here
/// is one the reference *answers*, so a typed defer is a failure, not a pass.
fn solve(src: &str) -> bool {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    match solve_goal(&ir, &scoped, &goal, &bounds, &SolveOptions::default()) {
        Ok(SolveVerdict::Sat(_)) => true,
        Ok(SolveVerdict::Unsat) => false,
        Ok(SolveVerdict::Unknown) => panic!("unbudgeted solve returned Unknown"),
        Err(e) => panic!("lowering/solve refused a cell the jar answers: {e:?}"),
    }
}

/// `run { <body> } for 3` against the M1/M2 base model.
fn base(body: &str) -> bool {
    solve(&format!("{BASE}run {{ {body} }} for 3\n"))
}

// ---------------------------- M1: the meta relations ------------------------

#[test]
fn m1_fields_and_subfields_are_different_relations() {
    // The discriminator the whole vocabulary turns on: `fields` is a sig's OWN
    // meta fields, `subfields` adds every descendant's. `V` owns `f`/`g` and
    // `W extends V` adds `h` (cells m1_01, m1_02, m1_03).
    assert!(base("#V$.subfields = 3"), "m1_01");
    assert!(base("#V$.fields = 2"), "m1_02");
    assert!(base("#W$.subfields = 1"), "m1_03");
}

#[test]
fn m1_meta_def_sig_arm_is_the_reflected_sig() {
    // `MetaDef::Sig`: `S$ <: value` denotes the concrete sig `S` (cell m1_06).
    assert!(base("V$.value = V"), "m1_06");
    // `W` extends `V`, so both `value`s live in the same type — and `V$.value`
    // is all of `V` while `W$.value` is only `W` (cell m1_30 is SAT because the
    // model may leave `W` equal to `V`).
    assert!(base("V$.value in univ"), "m1_29");
}

#[test]
fn m1_meta_def_field_arm_is_the_reflected_field() {
    // `MetaDef::Field`: `S$f <: value` denotes the field relation itself, at
    // one higher arity than the sig arm (cell m1_07).
    assert!(base("V$f.value = f"), "m1_07");
}

#[test]
fn m1_meta_def_metasigs_arm_unions_in_synthesis_order() {
    // `MetaDef::MetaSigs`: the union of the collected meta sigs (cells m1_23,
    // m1_04, m1_32) — and `subfields` is genuinely `fields` plus the
    // descendants', not a re-derivation (m1_32 is the one cell that ties the
    // two together).
    assert!(base("V$.fields = V$f + V$g"), "m1_23");
    assert!(base("W$.parent = V$"), "m1_04");
    assert!(base("V$.subfields = V$.fields + W$.subfields"), "m1_32");
}

#[test]
fn m1_meta_def_metasigs_arm_is_empty_for_a_fieldless_leaf() {
    // The empty union — `Z` has no fields and no parent, so three of its four
    // relations are `none` (cells m1_13, m1_05). `EMPTYNESS` keeps a `univ`
    // right column, which is why these are well-typed rather than rejected.
    assert!(base("no Z$.fields and no Z$.subfields"), "m1_13");
    assert!(base("no V$.parent"), "m1_05");
}

#[test]
fn m1_empty_meta_relation_is_unsatisfiable_not_untyped() {
    // The negative space of the empty union: a `univ` right column makes these
    // well-typed comparisons that simply cannot hold (cells m1_21, m1_31).
    assert!(!base("some V$.parent"), "m1_21");
    assert!(!base("Z$ in V$.parent"), "m1_31");
}

#[test]
fn m1_meta_sig_populations() {
    // The families themselves, so a mis-synthesized atom set fails here rather
    // than as a puzzling fold verdict (cells m1_08, m1_09, m1_12).
    assert!(base("#sig$ = 3"), "m1_08");
    assert!(base("#field$ = 3"), "m1_09");
    assert!(base("V$ in sig$ and V$f in field$"), "m1_12");
}

// ---------------------------- M2: the ground expansion ----------------------

#[test]
fn m2_the_three_expanding_binders() {
    // The three folds the phase-8 guard admits, on the same bound (cells m2_01,
    // m2_02, m2_03). All three are SAT: the model may leave every field empty,
    // may fill one, and `V$.subfields` always has exactly three members.
    assert!(base("all fx: V$.subfields | some fx.value"), "m2_01");
    assert!(base("some fx: V$.subfields | some fx.value"), "m2_02");
    assert!(base("#{ fx: V$.subfields | some fx.value } = 3"), "m2_03");
}

#[test]
fn m2_body_may_use_the_binding_outside_value() {
    // The expansion binds the variable to a real meta atom, so the body can use
    // it as an ordinary relation (cells m2_15, m2_18).
    assert!(base("all fx: V$.subfields | fx in field$"), "m2_15");
    assert!(base("all sx: V$ | sx.value = V"), "m2_18");
}

#[test]
fn m2_both_atom_families_run_for_a_union_bound() {
    // `sig$ + field$` admits both families, so the fold has six terms — one per
    // meta atom (cell m2_17).
    assert!(base("all x: sig$ + field$ | x in univ"), "m2_17");
    // …and each family alone still runs (cells m2_16, m2_37).
    assert!(base("all sx: sig$ | sx.value in univ"), "m2_16");
    assert!(base("all fx: field$ | some fx.value"), "m2_37");
}

#[test]
fn m2_expansions_nest() {
    // Two expansions, the inner one re-resolved under each outer binding —
    // nine copies of the body in all (cell m2_19).
    assert!(
        base("all fx: V$.subfields | all gx: V$.subfields | fx = gx or fx != gx"),
        "m2_19"
    );
}

#[test]
fn m2_expansion_inside_a_pred_with_ordinary_params() {
    // The corpus shape (hc7, einstein): the expansion sits in a pred body whose
    // own parameters are ordinary sigs, and folds within that body — meta names
    // can never appear in a declaration, so it never crosses the boundary
    // (cell m2_48, NOTES.md §M2 SURPRISE 5).
    let src = "abstract sig V { f: lone V, g: lone V }\n\
         sig W extends V { h: lone W }\n\
         pred sameAll[v1, v2: V] { all fx: V$.subfields | v1.(fx.value) = v2.(fx.value) }\n\
         run m2_48 { all disj a, b: V | not sameAll[a, b] } for 3\n";
    assert!(solve(src), "m2_48");
}

#[test]
fn m2_empty_folds() {
    // The empty fold is reachable through `field$` in a model with sigs and no
    // fields — NOT through `Z$.subfields`, whose `EMPTYNESS` type is not a meta
    // subtype at all (NOTES.md §M2 SURPRISE 4). Cells m2_33, m2_34, m2_35: the
    // empty `all` is `true`, the empty `some` is `false`, the empty
    // comprehension is `none`.
    let fieldless = |body: &str| solve(&format!("sig A {{}}\nrun {{ {body} }} for 3\n"));
    assert!(fieldless("all fx: field$ | some fx"), "m2_33");
    assert!(!fieldless("some fx: field$ | some fx"), "m2_34");
    assert!(fieldless("#{ fx: field$ | some fx } = 0"), "m2_35");
}

#[test]
fn m2_no_and_one_are_not_expanded() {
    // The guard admits only `all`/`some`/comprehension: `no`/`one` stay ordinary
    // quantifiers over the meta atoms. They are only *usable* when the body's
    // meta-relation names disambiguate on their own, which a single-field model
    // guarantees — hence `A` with one field (cells m2_28, m2_29, NOTES.md §M2
    // SURPRISE 2).
    let single = |body: &str| solve(&format!("sig A {{ r: lone A }}\nrun {{ {body} }} for 3\n"));
    assert!(single("no fx: A$.subfields | some fx.value"), "m2_28");
    assert!(single("one fx: A$.subfields | some fx.value"), "m2_29");
}

// ---------------------------- M5: the static$/var$ buckets ------------------

#[test]
fn m5_an_empty_bucket_is_forced_empty_by_its_synthesis_fact() {
    // The base model is fully static, so `var$` gets no members and the
    // synthesis mints `var$fact`. `out/m1_base_dump.txt` records exactly that:
    // `this/var$ META SUBSET([univ])` under `## root facts / fact var$fact` —
    // a NON-exact subset of `univ` whose emptiness comes from the fact alone,
    // not from its bounds. Without the fact `var$` floats and `some var$` is
    // wrongly SAT.
    assert!(!base("some var$"), "m1_base_dump root fact var$fact");
    assert!(base("no var$"), "m1_base_dump root fact var$fact");
    // The positive half, already jar-pinned as whole cells: `static$` is an
    // exact subset over all six meta sigs and is NOT emptied (m1_10, m1_11).
    assert!(base("some static$ and no var$"), "m1_10");
    assert!(base("#static$ = 6"), "m1_11");
}

#[test]
fn m5_variability_partitions_the_meta_sigs() {
    // Probe m5_01's own model, with its buckets read verbatim off
    // `out/m5_01_xml.txt`: `static$ = {B$$0, B$s$0}`, `var$ = {A$$0}`. Both
    // buckets are non-empty here, so the synthesis mints no emptiness fact at
    // all — the partition is doing the work, and this is the control showing
    // the previous test's fact is not just emptying `var$` unconditionally.
    let m5_01 = |body: &str| {
        solve(&format!(
            "var sig A {{}}\nsig B {{ s: lone B }}\nrun {{ {body} }} for 2\n"
        ))
    };
    assert!(m5_01("A$ in var$"), "m5_01 xml var$ = {{A$$0}}");
    assert!(m5_01("B$ in static$"), "m5_01 xml static$ ∋ B$$0");
    // `s` is not a `var` field, so `B$s` buckets static — the bucketing reads
    // the FIELD's variability, which is what SURPRISE 6's `var s` case turns on.
    assert!(m5_01("B$s in static$"), "m5_01 xml static$ ∋ B$s$0");
    assert!(
        m5_01("#var$ = 1 and #static$ = 2"),
        "m5_01 xml both buckets"
    );
    // The negative space: neither sig is in the other's bucket.
    assert!(!m5_01("A$ in static$"), "m5_01 xml A$$0 only in var$");
    assert!(!m5_01("B$ in var$"), "m5_01 xml B$$0 only in static$");
}

#[test]
fn p5_a_sigless_model_mints_all_three_emptiness_facts() {
    // The P5 closing probe (cells p5/p5_01..p5_03): a model with NO sigs still
    // trips the meta gate on the command's own `$` name, and `resolveMeta`
    // mints `sig$fact` + `static$fact` + `var$fact` (all three in the jar's
    // root-fact dump), so every meta bucket is forced empty.
    assert!(solve("run { no sig$ }\n"), "p5_01: jar SAT both modes");
    assert!(!solve("run { some sig$ }\n"), "p5_02: jar UNSAT both modes");
    assert!(
        solve("run { no field$ and no static$ and no var$ }\n"),
        "p5_03: jar SAT both modes"
    );
}

#[test]
fn p5_a_fieldless_sig_empties_only_the_field_bucket() {
    // Cell p5/p5_04: one fieldless static sig — `sig$`/`static$` are non-empty
    // (no fact minted for them), `field$` and `var$` still get theirs.
    assert!(
        solve("sig A {}\nrun { some sig$ and no field$ and some static$ }\n"),
        "p5_04: jar SAT both modes"
    );
}

#[test]
fn m2_expansion_is_deterministic() {
    // STYLE U4: the fold walks `bindings` (a `Vec`, in synthesis order) and the
    // `MetaSigs` unions walk their own `Vec`s, so nothing here can pick up a
    // hash order. Lower the same command twice and compare the emitted IR.
    let src = format!("{BASE}run {{ #{{ fx: V$.subfields | some fx.value }} = 3 }} for 3\n");
    let loader = MapLoader::new().with("root.als", &src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let render = || {
        let mut ir = Ir::default();
        let bounds = compute_bounds(&world, &scoped, &mut ir);
        let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
        format!("{:?}\n{:?}", goal.goal, ir.formulas)
    };
    assert_eq!(render(), render());
}
