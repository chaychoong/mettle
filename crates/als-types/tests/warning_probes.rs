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

// ---- A3/A4 (mt-118): the isSame non-firing family ----
//
// The reference's default `Expr.isSame` (no `ExprChoice` override) is pure
// reference identity, and every textual occurrence of an overloaded name/
// spine gets its own distinct `ExprChoice` object — so two occurrences that
// resolve to the identical candidate still fail the identity check, and the
// eq-/subset-redundant "same value" warning never fires.

#[test]
fn overloaded_util_integer_name_suppresses_eq_redundant_mt118() {
    // `pos` collides with the auto-opened `util/integer` pred `pos[n: Int]`
    // even though the field is declared once — two visible candidates at
    // name-collection time, so both occurrences wrap in their own choice.
    assert_no_warn(
        "sig A { pos: lone A }\nfact { pos = pos }\n",
        "eq-redundant",
    );
}

#[test]
fn non_colliding_name_still_warns_eq_redundant_mt118() {
    // Control for the probe above: `f` collides with nothing, so the ordinary
    // single-candidate shortcut applies and the redundancy still fires.
    assert_warns_at("sig A { f: lone A }\nfact { f = f }\n", "eq-redundant", 2);
}

#[test]
fn overloaded_join_suppresses_eq_redundant_mt118() {
    // `t.pos` reads as {join `t.pos`, call `pos[t]`} — two readings — so the
    // whole join node is choice-wrapped, exactly as the bare name is.
    assert_no_warn(
        "sig Track {}\nsig Train { pos: lone Track }\nfact { all t: Train | t.pos = t.pos }\n",
        "eq-redundant",
    );
}

#[test]
fn overloaded_field_join_suppresses_eq_redundant_mt118() {
    // `position` is declared on two sigs (no util/integer involvement at
    // all): every `c.position` occurrence is its own choice of two field
    // readings.
    assert_no_warn(
        concat!(
            "sig Component { position: lone Int }\n",
            "sig Robot { position: lone Int }\n",
            "fact { all c: Component | c.position = c.position }\n",
        ),
        "eq-redundant",
    );
}

#[test]
fn unique_field_join_still_warns_eq_redundant_mt118() {
    // Control: `position` declared on exactly one sig, so the join is never
    // choice-wrapped and the ordinary structural isSame recursion applies.
    assert_warns_at(
        concat!(
            "sig Component { position: lone Int }\n",
            "fact { all c: Component | c.position = c.position }\n",
        ),
        "eq-redundant",
        2,
    );
}

#[test]
fn domain_restrict_own_field_dereferences_to_subset_redundant_mt118() {
    // `Node<:adj` is exactly `adj`'s own declaring sig restricting `adj` — the
    // reference's DOMAIN-case optimization in `ExprBinary.Op.make` returns
    // `adj` itself, so `adj in Node<:adj` compares `adj` against `adj` by
    // identity.
    assert_warns_at(
        "sig Node { adj: set Node }\nfact { adj in Node<:adj }\n",
        "subset-redundant",
        2,
    );
}

#[test]
fn domain_restrict_other_sig_does_not_dereference_mt118() {
    // Control: `Other` is not `adj`'s declaring sig, so the reference's DOMAIN
    // optimization never fires and `Other<:adj` stays a genuine, distinct
    // node — no identity-based redundancy. (`Other` is disjoint from `Node`,
    // so `Other<:adj` is still statically empty and warns via the *other*
    // A4 disjunct — has-no-tuple — not via `isSame`; this probe pins that the
    // warning survives for the right reason, not the identity one.)
    assert_warns_at(
        concat!(
            "sig Node { adj: set Node }\n",
            "sig Other {}\n",
            "fact { adj in Other<:adj }\n",
        ),
        "subset-redundant",
        3,
    );
}

#[test]
fn disjoint_eq_redundant_independent_of_overload_mt118() {
    // Negative space: the DISJOINT branch (types provably disjoint) is
    // ORed alongside `same`, not gated by it, so it must keep firing even
    // when one side is an overloaded, choice-wrapped join (`t.pos` collides
    // with the auto-opened `util/integer` pred, same as the tests above) and
    // structurally can't be `same` as the other side anyway.
    assert_warns_at(
        concat!(
            "sig Track {}\n",
            "sig OtherSig {}\n",
            "sig Train { pos: lone Track }\n",
            "fact { all t: Train | t.pos = OtherSig }\n",
        ),
        "eq-redundant",
        4,
    );
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
