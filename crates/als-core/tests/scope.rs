//! Scope → universe tests (mt-029): the reference's `ScopeComputer` behavior,
//! one assertion per translation-ref §1 rule, plus atom-naming goldens whose
//! exact universes were jar-verified against Alloy 6.2.0 (probe harness
//! `scratchpad/probe/ProbeU.java`, reflecting `A4Solution.getBounds().universe`
//! — the full instance-independent universe). Every golden lists its probe.
//!
//! Loading uses the injected [`MapLoader`]; the embedded clean-room stdlib
//! (mt-015) supplies `util/ordering` for the enum golden.

use als_core::{compute_universe, ScopedUniverse, TranslateError};
use als_types::{resolve, MapLoader, ModuleGraph, ResolvedWorld};

/// Resolves `files` (first is `root.als`) and computes the universe of command
/// index `cmd` of the root.
fn scoped(files: &[(&str, &str)], cmd: usize) -> Result<ScopedUniverse, TranslateError> {
    let mut loader = MapLoader::new();
    for (name, src) in files {
        loader = loader.with(name, src);
    }
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let resolved = resolve(&graph).expect("resolve");
    let world: ResolvedWorld = resolved.world;
    compute_universe(&world, &world.commands[cmd])
}

/// The universe atom names of the single-command model `src`.
fn atoms(src: &str) -> Vec<String> {
    let su = scoped(&[("root.als", src)], 0).expect("compute_universe");
    su.universe.iter().map(|(_, n)| n.to_owned()).collect()
}

/// The single-command model's scope-phase error.
fn scope_err(src: &str) -> TranslateError {
    match scoped(&[("root.als", src)], 0) {
        Ok(_) => panic!("expected a TranslateError, got Ok\n--- src ---\n{src}"),
        Err(e) => e,
    }
}

/// The 16 integer atoms of the default bitwidth 4, in ascending order — every
/// universe ends with these (translation-ref §1.3).
fn ints4() -> Vec<String> {
    (-8..=7).map(|v: i64| v.to_string()).collect()
}

/// `[sig atoms…] ++ ints4`.
fn with_ints(sig_atoms: &[&str]) -> Vec<String> {
    let mut v: Vec<String> = sig_atoms.iter().map(|s| (*s).to_owned()).collect();
    v.extend(ints4());
    v
}

// ============================ §1.1 defaults ============================

#[test]
fn bare_run_defaults_to_overall_3() {
    // translation-ref §1.1: no overall + no per-sig scope ⇒ overall 3.
    assert_eq!(
        atoms("sig A {}\nrun {}\n"),
        with_ints(&["A$0", "A$1", "A$2"])
    );
}

#[test]
fn scalar_int_scope_does_not_suppress_default_overall() {
    // Probe pbwonly: `for 4 int` sets bitwidth only; the sig list is empty, so
    // overall still defaults to 3.
    assert_eq!(
        atoms("sig A {}\nrun {} for 4 int\n"),
        with_ints(&["A$0", "A$1", "A$2"])
    );
}

#[test]
fn run_and_check_scope_identically() {
    // translation-ref §1.1: ScopeComputer never branches on command kind.
    assert_eq!(atoms("sig A {}\nrun {}\n"), atoms("sig A {}\ncheck {}\n"));
}

#[test]
fn bitwidth_sets_int_atom_range() {
    // Probe p8int: `for 5 int` ⇒ 2^5 int atoms, -16 … 15.
    let a = atoms("sig A {}\nrun {} for 3 but 5 int\n");
    assert_eq!(&a[..3], &["A$0", "A$1", "A$2"]);
    assert_eq!(a[3], "-16");
    assert_eq!(*a.last().unwrap(), "15");
    assert_eq!(a.len(), 3 + 32);
}

// ======================= §1.2 declaration order =======================

#[test]
fn sig_atoms_follow_declaration_order() {
    // Probe p1: sigs B, A, C declared in that order ⇒ atoms in that order.
    assert_eq!(
        atoms("sig B {}\nsig A {}\nsig C { f: A }\nrun {} for 2\n"),
        with_ints(&["B$0", "B$1", "A$0", "A$1", "C$0", "C$1"])
    );
}

// ==================== §1.2 one / lone / some ====================

#[test]
fn multiplicity_sigs_force_their_scope() {
    // Probe p4: one⇒1 (exact), lone⇒≤1, some⇒overall, plain⇒overall.
    let su = scoped(
        &[(
            "root.als",
            "one sig A {}\nlone sig B {}\nsome sig C {}\nsig D {}\nrun {} for 3\n",
        )],
        0,
    )
    .unwrap();
    let names: Vec<String> = su.universe.iter().map(|(_, n)| n.to_owned()).collect();
    assert_eq!(
        names,
        with_ints(&["A$0", "B$0", "C$0", "C$1", "C$2", "D$0", "D$1", "D$2"])
    );
    // The `one` sig is exact; the plain sig is not.
    let sigs: Vec<_> = su.scopes.iter().collect();
    assert!(sigs[0].is_exact, "one sig A must be exact");
    assert_eq!(sigs[0].scope, 1);
    assert!(!sigs[3].is_exact, "plain sig D must be inexact");
    assert_eq!(sigs[3].scope, 3);
}

#[test]
fn lone_sig_keeps_explicit_zero() {
    // Probe plone0: `lone A` with explicit `0 A` stays 0 (not forced to 1).
    assert_eq!(
        atoms("lone sig A {}\nsig B {}\nrun {} for 3 but 0 A\n"),
        with_ints(&["B$0", "B$1", "B$2"])
    );
}

#[test]
fn one_sig_wrong_scope_rejected() {
    // Probe p15.
    let e = scope_err("one sig A {}\nrun {} for 3 but 2 A\n");
    assert!(
        matches!(e, TranslateError::OneSigScope { scope: 2, .. }),
        "{e:?}"
    );
}

#[test]
fn lone_sig_over_one_rejected() {
    // Probe plone2.
    let e = scope_err("lone sig A {}\nrun {} for 3 but 2 A\n");
    assert!(
        matches!(e, TranslateError::LoneSigScope { scope: 2, .. }),
        "{e:?}"
    );
}

#[test]
fn some_sig_zero_rejected() {
    // Probe psome0.
    let e = scope_err("some sig A {}\nrun {} for 0 A\n");
    assert!(matches!(e, TranslateError::SomeSigScope { .. }), "{e:?}");
}

// ==================== §1.2 exact ====================

#[test]
fn exactly_and_inexact_per_sig_scopes() {
    // Probe p5: `for exactly 2 A, 3 B` (no overall).
    let su = scoped(
        &[(
            "root.als",
            "sig A {}\nsig B {}\nrun {} for exactly 2 A, 3 B\n",
        )],
        0,
    )
    .unwrap();
    let names: Vec<String> = su.universe.iter().map(|(_, n)| n.to_owned()).collect();
    assert_eq!(names, with_ints(&["A$0", "A$1", "B$0", "B$1", "B$2"]));
    let sigs: Vec<_> = su.scopes.iter().collect();
    assert!(sigs[0].is_exact && sigs[0].scope == 2, "A exactly 2");
    assert!(!sigs[1].is_exact && sigs[1].scope == 3, "B inexact 3");
}

// ==================== §1.2 abstract-sum / difference ====================

#[test]
fn abstract_parent_mints_atoms_children_share_them() {
    // Probe p2: abstract A with children B,C for 3 ⇒ only A$0..A$2 (children
    // draw from the parent's pool, mint nothing).
    assert_eq!(
        atoms("abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 3\n"),
        with_ints(&["A$0", "A$1", "A$2"])
    );
}

#[test]
fn abstract_scope_is_sum_of_scoped_children() {
    // Probe psum: abstract A unscoped, B=2, C=3 ⇒ A=5.
    assert_eq!(
        atoms("abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 2 B, 3 C\n"),
        with_ints(&["A$0", "A$1", "A$2", "A$3", "A$4"])
    );
}

#[test]
fn abstract_difference_fills_missing_child() {
    // Probe pdiff: A=5, B=2, C unscoped ⇒ C=3, universe = A's 5 atoms. The
    // difference is observable through C's scope.
    let su = scoped(
        &[(
            "root.als",
            "abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 5 A, 2 B\n",
        )],
        0,
    )
    .unwrap();
    let names: Vec<String> = su.universe.iter().map(|(_, n)| n.to_owned()).collect();
    assert_eq!(names, with_ints(&["A$0", "A$1", "A$2", "A$3", "A$4"]));
    // sigs: A, B, C in declaration order; C got 5 - 2 = 3.
    let sigs: Vec<_> = su.scopes.iter().collect();
    assert_eq!(sigs[2].scope, 3, "C scope = A(5) - B(2)");
}

#[test]
fn abstract_two_unscoped_children_take_overall() {
    // Probe pabs2: abstract A, B,C both unscoped, for 4 ⇒ A=4 (abstract-sum
    // cannot fire; overall applies).
    assert_eq!(
        atoms("abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 4\n"),
        with_ints(&["A$0", "A$1", "A$2", "A$3"])
    );
}

// ==================== §1.2 parent inheritance ====================

#[test]
fn child_scope_over_parent_draws_from_parent_pool() {
    // Probe p6: `for 2 A, 3 B` (B extends A) ⇒ universe = A's 2 atoms; B's
    // larger explicit scope does not mint fresh atoms and is not an error.
    assert_eq!(
        atoms("sig A {}\nsig B extends A {}\nrun {} for 2 A, 3 B\n"),
        with_ints(&["A$0", "A$1"])
    );
}

// ==================== §1.2 scope errors ====================

#[test]
fn scope_on_univ_or_none_rejected_at_parse() {
    // Probe p8univ/p8none: the reference throws these *before* translation; in
    // mettle the parser (mt-011) owns them, so they never reach the scope
    // phase. Assert the pipeline still rejects, from the parse phase.
    for src in [
        "sig A {}\nrun {} for 3 but 2 univ\n",
        "sig A {}\nrun {} for 3 but 2 none\n",
    ] {
        let loader = MapLoader::new().with("root.als", src);
        assert!(
            ModuleGraph::load("root.als", &loader).is_err(),
            "expected a parse-phase reject for: {src}"
        );
    }
}

#[test]
fn scope_on_subset_sig_rejected() {
    // Probe psubin / psubex: any explicit scope on an `in`/`=` sig is an error.
    let e = scope_err("sig A {}\nsig B in A {}\nrun {} for 3 but 2 B\n");
    assert!(matches!(e, TranslateError::ScopeOnSubset { .. }), "{e:?}");
}

#[test]
fn scope_on_enum_rejected() {
    // Probe p7b.
    let e = scope_err("enum Color { Red, Green, Blue }\nrun {} for 3 but 2 Color\n");
    assert!(matches!(e, TranslateError::ScopeOnEnum { .. }), "{e:?}");
}

#[test]
fn non_exact_string_scope_rejected() {
    // Probe p8str.
    let e = scope_err("sig A {}\nrun {} for 3 but 2 String\n");
    assert!(
        matches!(e, TranslateError::StringScopeNotExact { .. }),
        "{e:?}"
    );
}

#[test]
fn per_sig_scope_without_overall_requires_all_top_level() {
    // Probe p9: `for 2 A` leaves B (top-level) with no scope ⇒ error naming B.
    let e = scope_err("sig A {}\nsig B {}\nrun {} for 2 A\n");
    match e {
        TranslateError::MustSpecifyScope { name, .. } => assert_eq!(name, "B"),
        other => panic!("{other:?}"),
    }
}

#[test]
fn bitwidth_over_30_rejected() {
    let e = scope_err("sig A {}\nrun {} for 3 but 31 int\n");
    assert!(
        matches!(e, TranslateError::BitwidthTooLarge { bitwidth: 31, .. }),
        "{e:?}"
    );
}

// ==================== atom-naming goldens (jar-verified) ====================

#[test]
fn enum_universe_golden() {
    // Probe p7: enum members are `one` sigs (one atom each); the auto-opened
    // util/ordering contributes its `one sig Ord`, named by its module alias.
    assert_eq!(
        atoms("enum Color { Red, Green, Blue }\nrun {} for 3\n"),
        with_ints(&["Red$0", "Green$0", "Blue$0", "ordering/Ord$0"])
    );
}

#[test]
fn opened_module_sig_atoms_are_alias_qualified() {
    // Probe popen: an opened-module sig's atoms carry the open alias prefix.
    let root = "open lib/foo\nsig A {}\nrun {} for 2\n";
    let foo = "module lib/foo\nsig Widget {}\n";
    let su = scoped(&[("root.als", root), ("lib/foo.als", foo)], 0).unwrap();
    let names: Vec<String> = su.universe.iter().map(|(_, n)| n.to_owned()).collect();
    assert_eq!(
        names,
        with_ints(&["A$0", "A$1", "foo/Widget$0", "foo/Widget$1"])
    );
}

#[test]
fn nested_module_sig_atoms_accumulate_alias_path() {
    // Probe pnest: root → a → b ⇒ b's sig is `a/b/Beta`.
    let root = "open lib/a\nsig Root {}\nrun {} for 2\n";
    let a = "module lib/a\nopen lib/b\nsig Alpha {}\n";
    let b = "module lib/b\nsig Beta {}\n";
    let su = scoped(&[("root.als", root), ("lib/a.als", a), ("lib/b.als", b)], 0).unwrap();
    let names: Vec<String> = su.universe.iter().map(|(_, n)| n.to_owned()).collect();
    assert_eq!(
        names,
        with_ints(&[
            "Root$0",
            "Root$1",
            "a/Alpha$0",
            "a/Alpha$1",
            "a/b/Beta$0",
            "a/b/Beta$1",
        ])
    );
}

// ==================== determinism (STYLE D1/U4) ====================

#[test]
fn universe_is_byte_stable_across_runs() {
    let src = "abstract sig A {}\nsig B extends A {}\none sig C {}\nsig D in A {}\nrun {} for 3\n";
    assert_eq!(atoms(src), atoms(src));
}

#[test]
fn scope_table_covers_every_non_builtin_prim_sig() {
    // The seam mt-030 relies on: a scope entry for every prim user sig (subset
    // sigs and builtins excluded), with a minted range exactly for the sigs
    // that own atoms.
    let su = scoped(
        &[(
            "root.als",
            "abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 3\n",
        )],
        0,
    )
    .unwrap();
    // A, B, C are prim ⇒ three entries; A mints (top-level), B/C do not.
    assert_eq!(su.scopes.len(), 3);
    let sigs: Vec<_> = su.scopes.iter().collect();
    assert!(sigs[0].minted.is_some(), "abstract parent A mints its pool");
    assert!(sigs[1].minted.is_none(), "child B draws from A");
    assert!(sigs[2].minted.is_none(), "child C draws from A");
    assert_eq!(su.sig_atom_count, 3);
    assert_eq!(su.int_atom_range().len(), 16);
}

// ==================== §1.2 scope raise (children exceed parent) ====================

#[test]
fn parent_scope_raised_to_children_lower_sum() {
    // The reference's `computeLowerBound` silently RAISES a sig's scope to the
    // sum of its children's lower bounds (`if (n < lower) n = lower`),
    // exactness preserved — never an error (jar-verified 2026-07-16, probe
    // B19: universe = C$0..C$2 only, no P atoms, command solves SAT).
    let su = scoped(
        &[(
            "root.als",
            "sig P {}\nsig C extends P {}\nrun {} for exactly 2 P, exactly 3 C\n",
        )],
        0,
    )
    .expect("the jar accepts an over-full exact child: scope raise, not error");
    assert_eq!(
        su.universe
            .iter()
            .map(|(_, n)| n.to_owned())
            .collect::<Vec<_>>(),
        with_ints(&["C$0", "C$1", "C$2"])
    );
    let entries: Vec<_> = su.scopes.iter().collect();
    let p = entries[0];
    assert_eq!(p.scope, 3, "P raised from 2 to the children lower sum");
    assert!(p.is_exact, "the raise preserves exactness");
    assert!(p.minted.is_none(), "raised-to-lower P mints nothing");
    let c = entries[1];
    assert_eq!((c.scope, c.is_exact), (3, true));
}

#[test]
fn inexact_parent_scope_raised_too() {
    // Same raise for an inexact parent (`<=2` raised to `<=3`, jar reporter
    // message "scope raised from <=2 to be <=3"); probe B19.
    let su = scoped(
        &[(
            "root.als",
            "sig P {}\nsig C extends P {}\nrun {} for 2 P, exactly 3 C\n",
        )],
        0,
    )
    .expect("raise, not error");
    let p = su.scopes.iter().next().expect("P entry");
    assert_eq!((p.scope, p.is_exact), (3, false));
}

#[test]
fn abstract_unscoped_children_both_inherit_parent_scope() {
    // Probe S1 / T5 semantics (mt-033 review fix): the derivation rules run as
    // full passes, so BOTH unscoped children inherit the parent's scope in one
    // rule-3 sweep — the abstract-difference rule must never back-derive the
    // second child to 0 from a half-updated state (the mt-029 per-change
    // restart bug behind 11 wrong baseline UNSATs).
    let su = scoped(
        &[(
            "root.als",
            "abstract sig A {}\nsig B extends A {}\nsig C extends A {}\nrun {} for 3\n",
        )],
        0,
    )
    .expect("scopes derive");
    let entries: Vec<_> = su.scopes.iter().collect();
    assert_eq!(
        entries.iter().map(|s| s.scope).collect::<Vec<_>>(),
        vec![3, 3, 3],
        "A, B, C all scope 3 — never C=0"
    );
}
