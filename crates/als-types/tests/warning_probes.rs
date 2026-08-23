//! Warning-parity regression suite (mt-023): one minimal model per §5.2 warning
//! class, each asserting mettle emits the expected [`ResolveWarning`] class at
//! the expected source line. Every model here was verified against the
//! reference jar (Alloy 6.2.0) via `ResolveGaugeShim` — the jar emits the same
//! warning at the same line (columns differ for binary operators: the reference
//! points at the operator glyph, mettle at the node start; see
//! `docs/reference/warning-parity.md`). Warnings never change the ACCEPT
//! verdict (LEDGER-002), so every model here also ACCEPTs.

use als_types::{resolve, MapLoader, ModuleGraph, ResolveWarning};

/// Resolves `src` as `root.als` and returns each warning's `(class, line)`
/// (1-based line), in span order. Panics if the model REJECTS (these are all
/// accept-with-warning models).
fn warns(src: &str) -> Vec<(&'static str, usize)> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let resolved = resolve(&graph).expect("expected ACCEPT (warnings never reject)");
    resolved
        .warnings
        .iter()
        .map(|w| (w.class(), line_of(src, w.span().start)))
        .collect()
}

/// 1-based line of byte `offset` in `src`.
#[allow(clippy::naive_bytecount)]
fn line_of(src: &str, offset: u32) -> usize {
    1 + src.as_bytes()[..offset as usize]
        .iter()
        .filter(|&&b| b == b'\n')
        .count()
}

/// Asserts some warning of `class` fired at `line`.
fn assert_warns_at(src: &str, class: &str, line: usize) {
    let ws = warns(src);
    assert!(
        ws.iter().any(|&(c, l)| c == class && l == line),
        "expected `{class}` at line {line}, got {ws:?}\n--- src ---\n{src}"
    );
}

/// Asserts no warning of `class` fired anywhere.
fn assert_no_warn(src: &str, class: &str) {
    let ws = warns(src);
    assert!(
        !ws.iter().any(|&(c, _)| c == class),
        "expected no `{class}`, got {ws:?}\n--- src ---\n{src}"
    );
}

/// Byte offsets of the unused-variable warnings, in emission order. Used where
/// two binders share a source line and only the *span* separates them.
fn unused_offsets(src: &str) -> Vec<u32> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let resolved = resolve(&graph).expect("expected ACCEPT (warnings never reject)");
    resolved
        .warnings
        .iter()
        .filter(|w| w.class() == "unused-var")
        .map(|w| w.span().start)
        .collect()
}

/// Asserts the unused-variable warnings land on exactly the `n`th occurrences
/// of `needle` in `src` (0-based, in source order).
fn assert_unused_at_occurrences(src: &str, needle: &str, occurrences: &[usize]) {
    let mut want = Vec::new();
    let mut from = 0;
    let mut seen = 0;
    while let Some(rel) = src[from..].find(needle) {
        let at = from + rel;
        if occurrences.contains(&seen) {
            want.push(u32::try_from(at).expect("offset fits"));
        }
        seen += 1;
        from = at + needle.len();
    }
    assert_eq!(want.len(), occurrences.len(), "needle `{needle}` not found");
    assert_eq!(
        unused_offsets(src),
        want,
        "unused-var spans\n--- src ---\n{src}"
    );
}

// ---- B: unused binder ----

#[test]
fn unused_quantifier_var_mt023() {
    assert_warns_at("sig A {}\nfact { all x: A | some A }\n", "unused-var", 2);
}

#[test]
fn unused_let_var_mt023() {
    assert_warns_at("sig A {}\nfact { let x = A | some A }\n", "unused-var", 2);
}

#[test]
fn used_via_join_spine_head_not_flagged_mt023() {
    // `proc.p` uses `p` as a join spine head — a syntactic use, not unused.
    assert_no_warn(
        "sig P {}\none sig O { proc: P -> P }\nfact { all p: P | lone O.proc.p }\n",
        "unused-var",
    );
}

#[test]
fn comprehension_var_never_flagged_mt023() {
    // `ExprQt.resolve` exempts comprehensions from the unused-var warning.
    assert_no_warn("sig A {}\nfact { some { x: A | some A } }\n", "unused-var");
}

// ---- B (mt-118): the overload-collapse and duplicate-binder subfamilies ----
//
// Both mechanisms are the reference's `hasVar` reading the *resolved* tree by
// binder identity, so a variable can be textually present yet unreferenced.

/// The alloy4fun `projects` shape (031193.als:74 vs :101), reduced: one
/// overloaded field, two quantifiers, opposite outcomes.
const OVERLOADED_PROJECTS: &str = concat!(
    "sig Project {}\n",
    "sig Person { projects: set Project }\n",
    "sig Student extends Person {}\n",
    "sig Course { projects: set Project }\n",
);

#[test]
fn overload_collapse_erases_the_binder_mt118() {
    // `Project` is disjoint from both declarers of `projects`, so every reading
    // of `pr.projects` is empty at arity 1 and `resolveHelper` replaces the whole
    // join with `none` — `pr` is gone from the resolved tree before `hasVar`.
    assert_warns_at(
        &format!("{OVERLOADED_PROJECTS}fact {{ all pr: Project | some pr.projects }}\n"),
        "unused-var",
        5,
    );
}

#[test]
fn surviving_overloaded_reading_keeps_the_binder_mt118() {
    // Same field, same file shape: `Student` is under `Person`, so the
    // `Person <: projects` reading survives the exact-match filter alone and the
    // join resolves normally — no collapse, `s` is used.
    assert_no_warn(
        &format!("{OVERLOADED_PROJECTS}fact {{ all s: Student | lone s.projects }}\n"),
        "unused-var",
    );
}

#[test]
fn collapse_does_not_hide_a_use_elsewhere_mt118() {
    // Negative space: the fold erases only its own subtree. `pr` occurs both
    // inside the collapsed join and outside it, so it stays used.
    assert_no_warn(
        &format!(
            "{OVERLOADED_PROJECTS}fact {{ all pr: Project | some pr.projects and pr in Project }}\n"
        ),
        "unused-var",
    );
}

#[test]
fn duplicate_binder_flags_the_shadowed_one_mt118() {
    // `all x: A, x: B | …`: the body's `x` is the second binder's, so only the
    // first is unreferenced (148377.als:34's shape).
    assert_unused_at_occurrences(
        "sig A {}\nsig B { f: set A }\nfact { all x: A, x: B | some x.f }\n",
        "x",
        &[0],
    );
}

#[test]
fn later_decl_bound_keeps_the_shadowed_binder_alive_mt118() {
    // 049900.als:84's shape: decl 2's bound `A - p` references `p`, so `p` is
    // used even though the body never names it; the first `k` still warns
    // because neither `B` nor the body reaches it.
    assert_unused_at_occurrences(
        "sig A {}\nsig B {}\nfact { all p: A, k: A - p, k: B | some k }\n",
        "k",
        &[0],
    );
}

#[test]
fn duplicate_names_within_one_decl_mt118() {
    // 130578.als:40's shape: both `u`s are in one name list, and the later one
    // wins the environment, so the first is unreferenced.
    assert_unused_at_occurrences("sig U {}\nfact { all disj u, u: U | some u }\n", "u", &[0]);
}

// ---- A1/A2: closure ----

#[test]
fn closure_disjoint_domain_range_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\none sig O { r: A -> B }\nfact { some ^(O.r) }\n",
        "closure-redundant",
        4,
    );
}

// ---- A3: equality redundancy ----

#[test]
fn eq_disjoint_mt023() {
    assert_warns_at("sig A {}\nsig B {}\nfact { A = B }\n", "eq-redundant", 3);
}

#[test]
fn eq_same_value_mt023() {
    assert_warns_at("sig A {}\nfact { A = A }\n", "eq-redundant", 2);
}

// ---- A4: subset redundancy ----

#[test]
fn subset_disjoint_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\nfact { A in B }\n",
        "subset-redundant",
        3,
    );
}

// ---- A6: intersection ----

#[test]
fn intersect_disjoint_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\nfact { no (A & B) }\n",
        "intersect-irrelevant",
        3,
    );
}

// ---- A9: join always empty ----

#[test]
fn join_empty_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\none sig O { f: A -> B }\nfact { no B.(O.f) }\n",
        "join-empty",
        4,
    );
}

// ---- A5: int atoms ----

#[test]
fn int_atoms_sum_mt023() {
    assert_warns_at("sig A {}\nfact { sum A > 0 }\n", "int-atoms", 2);
}

// ---- E: static/variable sig mismatch ----

#[test]
fn static_sig_variable_parent_mt023() {
    assert_warns_at(
        "var sig A {}\nsig B extends A {}\n",
        "sig-static-var-parent",
        2,
    );
}

#[test]
fn redundant_var_prim_only_mt023() {
    // `var` sig extending a static sig → redundant-var warning.
    assert_warns_at("sig A {}\nvar sig B extends A {}\n", "sig-redundant-var", 2);
}

#[test]
fn subset_var_never_redundant_mt023() {
    // A subset (`in`) var sig under a static parent does NOT warn redundant-var
    // (the reference's redundant-`var` branch is prim-`extends` only).
    assert_no_warn("sig A {}\nvar sig B in A {}\n", "sig-redundant-var");
}

// ---- F: function return disjoint ----

#[test]
fn function_return_disjoint_mt023() {
    assert_warns_at(
        "sig A {}\nsig B {}\nfun f: A { B }\nfact { some f }\n",
        "return-disjoint",
        3,
    );
}

// ---- warnings never change the verdict (LEDGER-002) ----

#[test]
fn warnings_accept_mt023() {
    // Every warning model ACCEPTs — a warning is never fatal.
    for src in [
        "sig A {}\nfact { all x: A | some A }\n",
        "sig A {}\nsig B {}\nfact { A = B }\n",
        "sig A {}\nsig B {}\nfact { no (A & B) }\n",
    ] {
        let loader = MapLoader::new().with("root.als", src);
        let graph = ModuleGraph::load("root.als", &loader).expect("load");
        assert!(resolve(&graph).is_ok(), "warning turned fatal:\n{src}");
    }
}

// keep the import used even if a variant set shrinks
#[allow(dead_code)]
fn _assert_type(_: &ResolveWarning) {}
