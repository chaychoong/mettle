//! IR lowering + goal-assembly tests (mt-031, translation-ref §2).
//!
//! Two kinds of check:
//!  1. **jar-verified goldens** — for small hand-written models spanning the §2
//!     tables, the reference Alloy 6.2.0 jar's exact Kodkod goal was dumped
//!     (`scratchpad/probe/DumpK2.java`, `debugExtractKInput()`, symmetry 0,
//!     noOverflow false, inferPartialInstance false) and is quoted in each test.
//!     mettle's lowered IR is asserted **semantically congruent** — structure
//!     modulo the documented divergences (translation-ref §10.3): no
//!     skolemization, n-ary vs balanced-binary `and`/`or`, no reflexive `r = r`
//!     padding, field domain+multiplicity grouped in one conjunct, and the
//!     jar's redundant per-arrow-column membership constraints omitted (entailed
//!     by the top-level `in`). The tests **do not run the jar** — the expected
//!     shape is pinned as a string here (STYLE U3).
//!  2. **unit checks** per §2 mapping row on the IR structure.
//!
//! The comparison is over a deterministic pretty-print of the goal formula
//! (relation names as the builder names them: `A`, `A.f`, `Int`, …).

use als_core::ir::{
    FormulaId, FormulaKind, IntCmpOp, IntExprId, IntExprKind, Ir, MultTest, QuantKind, RelBinOp,
    RelCmpOp, RelConst, RelExprId, RelExprKind, RelUnOp,
};
use als_core::{compute_bounds, compute_universe, lower_command, GoalConjunct, TranslateError};
use als_types::{resolve, MapLoader, ModuleGraph};

/// Resolve `src`, lower command 0, and return the goal conjuncts + IR.
fn build(src: &str) -> (Ir, Vec<GoalConjunct>) {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    let goal = lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).expect("lower");
    (ir, goal.conjuncts)
}

/// Attempt to lower command 0, returning the typed error if it defers.
fn try_build(src: &str) -> Result<(), TranslateError> {
    let loader = MapLoader::new().with("root.als", src);
    let graph = ModuleGraph::load("root.als", &loader).expect("load");
    let world = resolve(&graph).expect("resolve").world;
    let scoped = compute_universe(&world, &graph, &world.commands[0]).expect("universe");
    let mut ir = Ir::default();
    let bounds = compute_bounds(&world, &scoped, &mut ir);
    lower_command(&world, &graph, &scoped, &bounds, &mut ir, 0).map(|_| ())
}

/// The pretty-printed command conjunct (the last one).
fn command_str(ir: &Ir, conjuncts: &[GoalConjunct]) -> String {
    let c = conjuncts
        .iter()
        .rev()
        .find(|c| matches!(c.provenance, als_core::Provenance::Command))
        .expect("command conjunct");
    pf(ir, c.formula)
}

/// All conjuncts, pretty-printed, joined by ` && `.
fn all_str(ir: &Ir, conjuncts: &[GoalConjunct]) -> String {
    conjuncts
        .iter()
        .map(|c| pf(ir, c.formula))
        .collect::<Vec<_>>()
        .join(" && ")
}

/// The pretty-printed field-group `disj` conjunct (the single `FieldDisjFact`).
fn disj_str(ir: &Ir, conjuncts: &[GoalConjunct]) -> String {
    let c = conjuncts
        .iter()
        .find(|c| matches!(c.provenance, als_core::Provenance::FieldDisjFact(_)))
        .expect("field-disj conjunct");
    pf(ir, c.formula)
}

/// The pretty-printed first `Fact` conjunct.
fn fact_str(ir: &Ir, conjuncts: &[GoalConjunct]) -> String {
    let c = conjuncts
        .iter()
        .find(|c| matches!(c.provenance, als_core::Provenance::Fact))
        .expect("fact conjunct");
    pf(ir, c.formula)
}

// ---------------------------------------------------------------------------
// jar-verified goldens
// ---------------------------------------------------------------------------

#[test]
fn golden_quant_all_and_set_field() {
    // model: sig Node { next: set Node }  pred p { all n: Node | n in n.next }  run p for 3
    // jar goal (DumpK2):
    //   (all p_this: Node | (p_this.next) in Node)
    //   and (Node.next . univ) in Node
    //   and (all p_n: Node | p_n in (p_n.next))
    let (ir, cj) =
        build("sig Node { next: set Node }\npred p { all n: Node | n in n.next }\nrun p for 3\n");
    // Field fact: `set` bound → membership only (no multiplicity) + domain.
    assert_eq!(
        all_str(&ir, &cj),
        "((all this: Node | (this . Node.next) in Node) and (Node.next . univ) in Node) \
         && (all n: Node | n in (n . Node.next))"
    );
}

#[test]
fn golden_default_field_is_one() {
    // sig A {} sig B { f: A } run { some A } for 3
    // jar: all this: B | one (this.f) and (this.f) in A  ;  (B.f.univ) in B  ;  some A
    let (ir, cj) = build("sig A {}\nsig B { f: A }\nrun { some A } for 3\n");
    assert_eq!(
        all_str(&ir, &cj),
        "((all this: B | ((this . B.f) in A and one (this . B.f))) and (B.f . univ) in B) \
         && some A"
    );
}

#[test]
fn golden_pred_call_is_inlined() {
    // pred sub[x: A] { some x.f }  pred q { all a: A | sub[a] }  run q
    // jar: the call vanishes — `all p_a: A | some (p_a.f)`.
    let (ir, cj) = build(
        "sig A { f: set A }\npred sub[x: A] { some x.f }\npred q { all a: A | sub[a] }\nrun q for 3\n",
    );
    assert_eq!(command_str(&ir, &cj), "(all a: A | some (a . A.f))");
}

#[test]
fn golden_int_equality_promotes_literal() {
    // sig A { n: one Int }  pred r { all a: A | a.n = 1 }  run r
    // jar: (a.n) = Int[1]  — the literal 1 is cast to its Int atom, set-compared.
    let (ir, cj) = build("sig A { n: one Int }\npred r { all a: A | a.n = 1 }\nrun r for 3\n");
    assert_eq!(command_str(&ir, &cj), "(all a: A | (a . A.n) = Int[1])");
}

#[test]
fn golden_check_negates_assertion() {
    // assert noSelf { all a: A | a not in a.f }  check noSelf
    // jar: the negated assertion body (SAT = counterexample). The `all a: A` sits
    // at negative polarity (under the check's `!`), so it is an effective
    // existential and first-order-skolemizes to `$noSelf_a` (mt-047, §15; the
    // skolem label is the checked assertion's name): the quantifier is dropped and
    // the decl becomes `($noSelf_a in A and one $noSelf_a) => body`, the whole
    // thing negated back to the counterexample form = a single `a` in `A` with
    // `a in a.f`.
    let (ir, cj) = build(
        "sig A { f: set A }\nassert noSelf { all a: A | a not in a.f }\ncheck noSelf for 3\n",
    );
    assert_eq!(
        command_str(&ir, &cj),
        "!((($noSelf_a in A and one $noSelf_a) => !($noSelf_a in ($noSelf_a . A.f))))"
    );
}

#[test]
fn golden_arrow_right_one_multiplicity() {
    // sig B { f: A -> one A } — the `-> one` becomes a per-column `all a | one (a.f)`.
    // jar also emits redundant per-column membership (`(v.f) in A`) entailed by
    // the top-level `in (A->A)`; mettle omits those (documented divergence).
    let (ir, cj) = build("sig A {}\nsig B { f: A -> one A }\nrun { some B } for 3\n");
    let field = pf(&ir, cj[0].formula);
    assert!(
        field.contains("(this . B.f) in (A -> A)"),
        "membership: {field}"
    );
    assert!(
        field.contains("all _c0: A | one (_c0 . (this . B.f))"),
        "right-one column mult: {field}"
    );
    // Domain, projected twice for the arity-3 field.
    assert!(
        field.contains("((B.f . univ) . univ) in B"),
        "domain: {field}"
    );
}

// -- mt-039: nested multiplicity arrows in field bounds ---------------------
//
// Jar-verified 2026-07-17 (`scratchpad/probe/nested/n1..n7`, `DumpK2`, symmetry
// 0, noOverflow false, inferPartialInstance false) — translation-ref §10.3
// probes n1-n7. All models: `sig A {} sig B {} sig C {} sig S { f: <bound> }
// run {} for 3` (n6 adds `sig D {}`). The recursive rule (§2.1): a marked side
// that is itself an arrow recurses fully rather than testing one multiplicity
// (probe n1); a compound side (no single named relation) is destructured into
// fresh `univ` leaf variables guarded by its own recursive constraint on the
// reconstructed tuple, because Kodkod can decl-bind one variable directly over
// a *named* relation of any arity but not over a literal nested product
// (probe n3); both an outer column mark and a nested recursion can coexist
// (probe n7). Per divergence (e), a column asserting nothing new (no mark,
// other side not an arrow) is omitted, at any recursion depth.

#[test]
fn golden_nested_arrow_right_nested_marked_inner() {
    // n1: f: A -> (B one -> one C)
    // jar: this.f in (A->B->C) and
    //   (all v0:A | v0.(this.f) in (B->C) and
    //     (all v1:B | one(v1.(v0.(this.f))) and (v1.(v0.(this.f))) in C) and
    //     (all v2:C | one((v0.(this.f)).v2) and ((v0.(this.f)).v2) in B)) and
    //   (all v3:univ,v4:univ | <guard> implies ((this.f).v3).v4 in A)
    // the outer A column is unmarked and the RHS-of-implies is bare
    // membership (divergence e) — mettle omits that whole redundant block.
    let (ir, cj) =
        build("sig A {}\nsig B {}\nsig C {}\nsig S { f: A -> (B one -> one C) }\nrun {} for 3\n");
    let field = pf(&ir, cj[0].formula);
    assert!(
        field.contains("(this . S.f) in (A -> (B -> C))"),
        "membership: {field}"
    );
    assert!(
        field.contains(
            "all _c0: A | ((_c0 . (this . S.f)) in (B -> C) \
            and (all _c1: B | one (_c1 . (_c0 . (this . S.f)))) \
            and (all _c2: C | one ((_c0 . (this . S.f)) . _c2)))"
        ),
        "recursive inner one/one columns: {field}"
    );
    assert!(
        !field.contains(": univ |"),
        "outer A column unmarked, other side plain -> fully redundant, omitted: {field}"
    );
}

#[test]
fn golden_nested_arrow_outer_marked_plain_inner() {
    // n2: f: A one -> (B -> C)
    // jar: this.f in (A->B->C) and (all v0:A | v0.(this.f) in (B->C)) and
    //   (all v1:univ,v2:univ | (v2->v1) in (B->C) implies
    //     (one(((this.f).v1).v2) and ((this.f).v1).v2 in A))
    // the inner B->C is flat/unmarked (right quantifier keeps only the
    // redundant-but-harmless recursive membership); the outer `one` survives
    // in the left quantifier over the compound RHS, destructured via fresh
    // univ leaves (Kodkod can't decl-bind one var over a literal product).
    let (ir, cj) =
        build("sig A {}\nsig B {}\nsig C {}\nsig S { f: A one -> (B -> C) }\nrun {} for 3\n");
    let field = pf(&ir, cj[0].formula);
    assert!(
        field.contains("(this . S.f) in (A -> (B -> C))"),
        "membership: {field}"
    );
    assert!(
        field.contains("all _c0: A | (_c0 . (this . S.f)) in (B -> C)"),
        "unmarked inner recursion (membership only): {field}"
    );
    assert!(
        field.contains(
            "all _c1: univ | (all _c2: univ | \
            ((_c1 -> _c2) in (B -> C) => one (((this . S.f) . _c2) . _c1)))"
        ),
        "outer `one` over the compound RHS, univ-leaf destructured: {field}"
    );
}

#[test]
fn golden_nested_arrow_left_nested() {
    // n3: f: (A -> B) one -> one C
    // jar: this.f in (A->B->C) and
    //   (all v0:univ,v1:univ | (v0->v1) in (A->B) implies
    //     (one(v1.(v0.(this.f))) and (v1.(v0.(this.f))) in C)) and
    //   (all v2:C | one((this.f).v2) and (this.f).v2 in (A->B))
    // the compound LHS is destructured for the right (rhs_mult) column; the
    // left (lhs_mult) column iterates the plain C directly.
    let (ir, cj) =
        build("sig A {}\nsig B {}\nsig C {}\nsig S { f: (A -> B) one -> one C }\nrun {} for 3\n");
    let field = pf(&ir, cj[0].formula);
    assert!(
        field.contains("(this . S.f) in ((A -> B) -> C)"),
        "membership: {field}"
    );
    assert!(
        field.contains(
            "all _c0: univ | (all _c1: univ | \
            ((_c0 -> _c1) in (A -> B) => one (_c1 . (_c0 . (this . S.f)))))"
        ),
        "compound-LHS right column, univ-leaf destructured: {field}"
    );
    assert!(
        field.contains(
            "all _c2: C | (one ((this . S.f) . _c2) \
            and ((this . S.f) . _c2) in (A -> B))"
        ),
        "left column over plain C, recursing into the compound LHS: {field}"
    );
}

#[test]
fn golden_nested_arrow_some_lone_columns() {
    // n4: f: A -> (B some -> lone C)
    // jar mirrors n1's shape with `lone`/`some` swapped in for `one`/`one`:
    //   (all v1:B | lone(...)) and (all v2:C | some(...))
    let (ir, cj) =
        build("sig A {}\nsig B {}\nsig C {}\nsig S { f: A -> (B some -> lone C) }\nrun {} for 3\n");
    let field = pf(&ir, cj[0].formula);
    assert!(
        field.contains(
            "all _c0: A | ((_c0 . (this . S.f)) in (B -> C) \
            and (all _c1: B | lone (_c1 . (_c0 . (this . S.f)))) \
            and (all _c2: C | some ((_c0 . (this . S.f)) . _c2)))"
        ),
        "some/lone column mult mapping preserved under recursion: {field}"
    );
}

#[test]
fn golden_nested_arrow_lone_outer() {
    // n5: f: A lone -> (B -> C) — mirrors n2 with `lone` instead of `one`.
    let (ir, cj) =
        build("sig A {}\nsig B {}\nsig C {}\nsig S { f: A lone -> (B -> C) }\nrun {} for 3\n");
    let field = pf(&ir, cj[0].formula);
    assert!(
        field.contains(
            "all _c1: univ | (all _c2: univ | \
            ((_c1 -> _c2) in (B -> C) => lone (((this . S.f) . _c2) . _c1)))"
        ),
        "outer `lone` over the compound RHS: {field}"
    );
}

#[test]
fn golden_nested_arrow_three_deep() {
    // n6: f: A -> (B -> (C one -> one D)) — three levels of recursion compose:
    // the outermost A/[B->(C->D)] column is fully unmarked on both sides (A
    // plain, unmarked) so it is omitted entirely (no `univ` leaves needed at
    // the top); the middle B/[C->D] column recurses one level further to
    // reach the innermost `one`/`one` on C, D.
    let (ir, cj) = build(
        "sig A {}\nsig B {}\nsig C {}\nsig D {}\n\
         sig S { f: A -> (B -> (C one -> one D)) }\nrun {} for 3\n",
    );
    let field = pf(&ir, cj[0].formula);
    assert!(
        field.contains("(this . S.f) in (A -> (B -> (C -> D)))"),
        "membership: {field}"
    );
    assert!(
        field.contains(
            "all _c0: A | ((_c0 . (this . S.f)) in (B -> (C -> D)) \
             and (all _c1: B | ((_c1 . (_c0 . (this . S.f))) in (C -> D) \
             and (all _c2: C | one (_c2 . (_c1 . (_c0 . (this . S.f))))) \
             and (all _c3: D | one ((_c1 . (_c0 . (this . S.f))) . _c3)))))"
        ),
        "three levels of recursion: {field}"
    );
    assert!(
        !field.contains(": univ |"),
        "every column along the way is unmarked except the innermost one/one \
         (checked via plain decl-bound vars, never needing univ leaves): {field}"
    );
}

#[test]
fn golden_nested_arrow_double_mark() {
    // n7: f: A -> some (B one -> one C) — an outer column mark AND a nested
    // arrow coexist: the jar (and mettle) emit BOTH the `some` mult test AND
    // the full recursive one/one structure on the same joined value.
    let (ir, cj) = build(
        "sig A {}\nsig B {}\nsig C {}\nsig S { f: A -> some (B one -> one C) }\nrun {} for 3\n",
    );
    let field = pf(&ir, cj[0].formula);
    assert!(
        field.contains(
            "all _c0: A | (some (_c0 . (this . S.f)) \
             and (_c0 . (this . S.f)) in (B -> C) \
             and (all _c1: B | one (_c1 . (_c0 . (this . S.f)))) \
             and (all _c2: C | one ((_c0 . (this . S.f)) . _c2)))"
        ),
        "outer `some` mult test AND the recursive inner one/one, both present: {field}"
    );
}

#[test]
fn golden_defined_field_equals_value() {
    // sig A { r: set A, s = r } — the defined field `s` becomes `this.s = this.r`.
    // jar: (this.s) = (this.r).
    let (ir, cj) = build("sig A { r: set A, s = r }\nrun { some A } for 3\n");
    let s_fact = pf(&ir, cj[1].formula);
    assert!(
        s_fact.contains("(this . A.s) = (this . A.r)"),
        "defined field: {s_fact}"
    );
}

#[test]
fn golden_disj_decl_guard() {
    // all disj x, y: A | x != y  ⇒ the disj guard is an antecedent for `all`.
    let (ir, cj) = build("sig A {}\npred p { all disj x, y: A | x != y }\nrun p for 3\n");
    assert_eq!(
        command_str(&ir, &cj),
        "(all x: A | (all y: A | (no (x & y) => !(x = y))))"
    );
}

#[test]
fn golden_field_disj_two_fields() {
    // sig E {} sig S { disj a, b: set E } run {} for 3
    // jar goal (DumpK2 probe p1): after both fields' mult+domain facts —
    //   no (this/S.a & this/S.b)
    let (ir, cj) = build("sig E {}\nsig S { disj a, b: set E }\nrun {} for 3\n");
    assert_eq!(disj_str(&ir, &cj), "no (S.a & S.b)");
}

#[test]
fn golden_field_disj_three_fields_staged() {
    // sig E {} sig S { disj a, b, c: set E } run {} for 3
    // jar goal (DumpK2 probe p2): the staged pairwise form
    //   no ((this/S.a + this/S.b) & this/S.c) and no (this/S.a & this/S.b)
    // (mettle emits the same conjuncts in incremental order, translation-ref
    // §10.3 divergence (b): `and` is associative).
    let (ir, cj) = build("sig E {}\nsig S { disj a, b, c: set E }\nrun {} for 3\n");
    assert_eq!(
        disj_str(&ir, &cj),
        "(no (S.a & S.b) and no ((S.a + S.b) & S.c))"
    );
}

#[test]
fn golden_field_disj_arity_two() {
    // sig E {} sig S { disj f, g: E -> E } run {} for 3
    // jar goal (DumpK2 probe p3): disjointness is over the full field relations
    //   no (this/S.f & this/S.g)
    let (ir, cj) = build("sig E {}\nsig S { disj f, g: E -> E }\nrun {} for 3\n");
    assert_eq!(disj_str(&ir, &cj), "no (S.f & S.g)");
}

#[test]
fn golden_field_disj_implicit_one() {
    // sig E {} sig S { disj a, b: E } run {} for 3
    // jar goal (DumpK2 probe p4): the implicit-`one` on each field does not
    // change the disj fact —
    //   no (this/S.a & this/S.b)
    let (ir, cj) = build("sig E {}\nsig S { disj a, b: E }\nrun {} for 3\n");
    assert_eq!(disj_str(&ir, &cj), "no (S.a & S.b)");
}

#[test]
fn field_disj_var_group_defers() {
    // sig E {} sig S { var disj a, b: set E } run {} for 3
    // jar goal (DumpK2 probe p5): each `no` is wrapped in `always` — temporal,
    // so the whole command defers (§2.3), never a silent drop / wrong verdict.
    let e = try_build("sig E {}\nsig S { var disj a, b: set E }\nrun {} for 3\n").unwrap_err();
    assert!(
        matches!(e, TranslateError::TemporalUnsupported { .. }),
        "{e:?}"
    );
}

#[test]
fn golden_cardinality_and_int_compare() {
    // #A = 2 and #A < 3.
    let (ir, cj) = build("sig A {}\npred p { #A = 2 and #A < 3 }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "(#A = 2 and #A < 3)");
}

#[test]
fn golden_reflexive_closure_star() {
    // a.*nx — `*` is the reflexive-transitive closure.
    let (ir, cj) = build("sig N { nx: set N }\npred p { all a, b: N | b in a.*nx }\nrun p for 3\n");
    assert_eq!(
        command_str(&ir, &cj),
        "(all a: N | (all b: N | b in (a . *(N.nx))))"
    );
}

#[test]
fn golden_domain_range_restrict() {
    // A <: f  and  f :> A  — product-pad-and-intersect (translation-ref §2.1).
    let (ir, cj) =
        build("sig A { f: set A }\npred p { some (A <: f) and some (f :> A) }\nrun p for 3\n");
    // A <: f = f & (A -> univ);  f :> A = f & (univ -> A).
    assert_eq!(
        command_str(&ir, &cj),
        "(some (A.f & (A -> univ)) and some (A.f & (univ -> A)))"
    );
}

#[test]
fn golden_sig_appended_fact_binds_this() {
    // sig A { f: set A } { f in f } — appended fact is `all this: A | this.f in this.f`.
    let (ir, cj) = build("sig A { f: set A } { f in f }\nrun { some A } for 3\n");
    let appended = cj
        .iter()
        .find(|c| matches!(c.provenance, als_core::Provenance::AppendedFact(_)))
        .expect("appended fact conjunct");
    assert_eq!(
        pf(&ir, appended.formula),
        "(all this: A | (this . A.f) in (this . A.f))"
    );
}

#[test]
fn golden_one_sig_field_owner_strip() {
    // one sig Cfg { limit: one A } — the field relation is `Cfg -> Cfg.limit`.
    let (ir, cj) =
        build("one sig Cfg { limit: one A }\nsig A {}\npred p { some Cfg.limit }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "some (Cfg . (Cfg -> Cfg.limit))");
}

#[test]
fn golden_subset_sig_bound_constraint() {
    // sig B in A {} — the `B in A` containment is a bounds constraint (mt-030),
    // present as a top-level conjunct; the command references B directly.
    let (ir, cj) = build("sig A {}\nsig B in A {}\npred p { some B and B in A }\nrun p for 3\n");
    assert!(
        cj.iter().any(
            |c| matches!(c.provenance, als_core::Provenance::BoundsConstraint)
                && pf(&ir, c.formula) == "B in A"
        ),
        "subset containment: {}",
        all_str(&ir, &cj)
    );
    assert_eq!(command_str(&ir, &cj), "(some B and B in A)");
}

// ---------------------------------------------------------------------------
// unit checks per §2 row
// ---------------------------------------------------------------------------

#[test]
fn run_pred_existentially_quantifies_params() {
    // run p where p[x: A] — the param is a top-level first-order existential,
    // skolemized to the constant relation `$p_x` (mt-047, §15): membership +
    // `one` + the body, all conjoined (the quantifier is dropped).
    let (ir, cj) = build("sig A { f: set A }\npred p[x: A] { some x.f }\nrun p for 3\n");
    assert_eq!(
        command_str(&ir, &cj),
        "($p_x in A and one $p_x and some ($p_x . A.f))"
    );
}

#[test]
fn no_quantifier_desugars_to_all_not() {
    // no x: A | φ  ⇒  all x: A | ¬φ.
    let (ir, cj) = build("sig A { f: set A }\npred p { no x: A | some x.f }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "(all x: A | !(some (x . A.f)))");
}

#[test]
fn one_quantifier_uses_comprehension_cardinality() {
    // one x: A | φ  ⇒  one { x: A | φ }.
    let (ir, cj) = build("sig A { f: set A }\npred p { one x: A | some x.f }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "one {x: A | some (x . A.f)}");
}

#[test]
fn comprehension_lowers_to_comprehension() {
    let (ir, cj) = build("sig A { f: set A }\npred p { some { x: A | some x.f } }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "some {x: A | some (x . A.f)}");
}

#[test]
fn relational_ops_and_transpose() {
    let (ir, cj) = build(
        "sig A { f: set A, g: set A }\npred p { some (f + g) and some (f & g) and some (f - g) and some ~f }\nrun p for 3\n",
    );
    // `and` is left-associative binary; the lowerer nests it (congruent to the
    // reference's balanced-binary `and`, translation-ref §2.2).
    assert_eq!(
        command_str(&ir, &cj),
        "(((some (A.f + A.g) and some (A.f & A.g)) and some (A.f - A.g)) and some ~(A.f))"
    );
}

#[test]
fn iden_univ_none_constants() {
    let (ir, cj) = build("sig A {}\npred p { some iden and some univ and no none }\nrun p for 3\n");
    // mt-053 (LEDGER-011, §10.8): `univ`/`iden` in a **user expression** lower to
    // the jar's *live union* `Int ∪ String ∪ ⋃(top-level sig denotes)` (here
    // `(Int + String) + A`), not the all-atoms constant; `iden` is that live set's
    // diagonal `iden & (live -> live)`. `none` is untouched. The all-atoms
    // `RelConst::{Univ, Iden}` survive only for the encoder's internal uses.
    assert_eq!(
        command_str(&ir, &cj),
        "((some (iden & (((Int + String) + A) -> ((Int + String) + A))) \
         and some ((Int + String) + A)) and no none)"
    );
}

#[test]
fn disj_builtin_staged_expansion() {
    // disj[A, B, C] ⇒ no(A&B) ∧ no((A+B)&C) (staged form, translation-ref §2.2).
    let (ir, cj) = build(
        "sig X {} sig A extends X {} sig B extends X {} sig C extends X {}\npred p { disj[A, B, C] }\nrun p for 3\n",
    );
    assert_eq!(command_str(&ir, &cj), "(no (A & B) and no ((A + B) & C))");
}

#[test]
fn let_binding_substitutes() {
    let (ir, cj) = build("sig A { f: set A }\npred p { let y = A.f | some y }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "some (A . A.f)");
}

#[test]
fn implies_iff_and_or() {
    let (ir, cj) = build(
        "sig A {}\npred p { (some A => some A) and (some A <=> some A) or no A }\nrun p for 3\n",
    );
    assert_eq!(
        command_str(&ir, &cj),
        "(((some A => some A) and (some A <=> some A)) or no A)"
    );
}

#[test]
fn sum_quantifier_lowers_to_int_sum() {
    let (ir, cj) = build("sig A { n: one Int }\npred p { (sum a: A | a.n) = 0 }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "(sum a: A | int[(a . A.n)]) = 0");
}

// ---------------------------------------------------------------------------
// typed defer errors (never a wrong verdict)
// ---------------------------------------------------------------------------

#[test]
fn temporal_operator_defers() {
    let e = try_build("sig A { f: set A }\npred p { always some A }\nrun p for 3\n").unwrap_err();
    assert!(
        matches!(e, TranslateError::TemporalUnsupported { .. }),
        "{e:?}"
    );
}

#[test]
fn prime_operator_defers() {
    let e = try_build("var sig A {}\npred p { some A' }\nrun p for 3\n").unwrap_err();
    assert!(
        matches!(e, TranslateError::TemporalUnsupported { .. }),
        "{e:?}"
    );
}

#[test]
fn string_literal_lowers() {
    // mt-045: a string literal now lowers to its singleton relation (no defer).
    try_build("sig A { s: one String }\npred p { all a: A | a.s = \"x\" }\nrun p for 3\n")
        .expect("string literal should lower");
}

#[test]
fn determinism_lower_twice_identical() {
    let src = "sig A { f: set A }\npred p { all a: A | some a.f }\nrun p for 3\n";
    let (ir1, cj1) = build(src);
    let (ir2, cj2) = build(src);
    assert_eq!(all_str(&ir1, &cj1), all_str(&ir2, &cj2));
}

// ---------------------------------------------------------------------------
// pretty-printer (test-only)
// ---------------------------------------------------------------------------

fn pf(ir: &Ir, f: FormulaId) -> String {
    match &ir.formulas[f].kind {
        FormulaKind::Const(b) => b.to_string(),
        FormulaKind::Not(x) => format!("!({})", pf(ir, *x)),
        FormulaKind::And(xs) => format!(
            "({})",
            xs.iter()
                .map(|&x| pf(ir, x))
                .collect::<Vec<_>>()
                .join(" and ")
        ),
        FormulaKind::Or(xs) => format!(
            "({})",
            xs.iter()
                .map(|&x| pf(ir, x))
                .collect::<Vec<_>>()
                .join(" or ")
        ),
        FormulaKind::Implies {
            antecedent,
            consequent,
        } => {
            format!("({} => {})", pf(ir, *antecedent), pf(ir, *consequent))
        }
        FormulaKind::Iff(a, b) => format!("({} <=> {})", pf(ir, *a), pf(ir, *b)),
        FormulaKind::RelCompare { op, lhs, rhs } => format!(
            "{} {} {}",
            pr(ir, *lhs),
            if matches!(op, RelCmpOp::Equal) {
                "="
            } else {
                "in"
            },
            pr(ir, *rhs)
        ),
        FormulaKind::IntCompare { op, lhs, rhs } => {
            format!("{} {} {}", pi(ir, *lhs), icmp(*op), pi(ir, *rhs))
        }
        FormulaKind::MultTest { test, expr } => format!("{} {}", mt(*test), pr(ir, *expr)),
        FormulaKind::Quant {
            kind,
            var,
            bound,
            body,
        } => format!(
            "({} {}: {} | {})",
            if matches!(kind, QuantKind::All) {
                "all"
            } else {
                "some"
            },
            ir.vars[*var].name,
            pr(ir, *bound),
            pf(ir, *body)
        ),
        FormulaKind::TemporalUnary { body, .. } => format!("<t>({})", pf(ir, *body)),
        FormulaKind::TemporalBinary { lhs, rhs, .. } => {
            format!("<t>({},{})", pf(ir, *lhs), pf(ir, *rhs))
        }
    }
}
fn pr(ir: &Ir, r: RelExprId) -> String {
    match &ir.rel_exprs[r].kind {
        RelExprKind::Relation(rel) => ir.relations[*rel].name.clone(),
        RelExprKind::Var(v) => ir.vars[*v].name.clone(),
        RelExprKind::Const(c) => match c {
            RelConst::None => "none".into(),
            RelConst::Univ => "univ".into(),
            RelConst::Iden => "iden".into(),
        },
        RelExprKind::Binary { op, lhs, rhs } => {
            let o = match op {
                RelBinOp::Union => "+",
                RelBinOp::Diff => "-",
                RelBinOp::Intersect => "&",
                RelBinOp::Join => ".",
                RelBinOp::Product => "->",
                RelBinOp::Override => "++",
            };
            format!("({} {} {})", pr(ir, *lhs), o, pr(ir, *rhs))
        }
        RelExprKind::Unary { op, expr } => {
            let o = match op {
                RelUnOp::Transpose => "~",
                RelUnOp::Closure => "^",
                RelUnOp::ReflexiveClosure => "*",
            };
            format!("{o}({})", pr(ir, *expr))
        }
        RelExprKind::Prime(e) => format!("({})'", pr(ir, *e)),
        RelExprKind::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => format!(
            "({} ? {} : {})",
            pf(ir, *cond),
            pr(ir, *then_branch),
            pr(ir, *else_branch)
        ),
        RelExprKind::Comprehension { decls, body } => format!(
            "{{{} | {}}}",
            decls
                .iter()
                .map(|d| format!("{}: {}", ir.vars[d.var].name, pr(ir, d.bound)))
                .collect::<Vec<_>>()
                .join(", "),
            pf(ir, *body)
        ),
        RelExprKind::IntToAtom(i) => format!("Int[{}]", pi(ir, *i)),
    }
}
fn pi(ir: &Ir, i: IntExprId) -> String {
    match &ir.int_exprs[i].kind {
        IntExprKind::Const(n) => n.to_string(),
        IntExprKind::Card(r) => format!("#{}", pr(ir, *r)),
        IntExprKind::AtomToInt(r) => format!("int[{}]", pr(ir, *r)),
        IntExprKind::Neg(x) => format!("-{}", pi(ir, *x)),
        IntExprKind::Binary { lhs, rhs, .. } => format!("({} <op> {})", pi(ir, *lhs), pi(ir, *rhs)),
        IntExprKind::Sum { var, bound, body } => format!(
            "(sum {}: {} | {})",
            ir.vars[*var].name,
            pr(ir, *bound),
            pi(ir, *body)
        ),
        IntExprKind::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => {
            format!("({} : {})", pi(ir, *then_branch), pi(ir, *else_branch))
        }
    }
}
fn mt(t: MultTest) -> &'static str {
    match t {
        MultTest::No => "no",
        MultTest::Some => "some",
        MultTest::Lone => "lone",
        MultTest::One => "one",
    }
}
fn icmp(o: IntCmpOp) -> &'static str {
    match o {
        IntCmpOp::Eq => "=",
        IntCmpOp::Lt => "<",
        IntCmpOp::Le => "=<",
        IntCmpOp::Gt => ">",
        IntCmpOp::Ge => ">=",
    }
}
// ---------------------------------------------------------------------------
// higher-order skolemization goldens (mt-038, translation-ref §10.6, probes T9)
// ---------------------------------------------------------------------------
// The jar dump (DumpK2) shows the quantifier before Kodkod's internal
// skolemization, with the skolem-named variable `<cmdLabel>_<var>`; mettle mints
// the free relation `$<cmdLabel>_<var>` directly at lowering and discharges the
// quantifier. Divergences (translation-ref §10.3): mettle omits the jar's
// redundant per-arrow-column memberships (e); and for a `check`-of-assert the
// resolved command carries no assert name, so the skolem falls back to `$<var>`
// (the reference names it `Inj_f`) — cosmetic only (instances are never diffed).

#[test]
fn golden_skolem_set_unary() {
    // run foo { some r: set A | some r } for 3
    // jar dump T9a: (some foo_r: set this/A | some foo_r) — Kodkod skolemizes
    // `foo_r` to a free relation ⊆ upper(A); replacement = `$foo_r in A` ∧ body.
    let (ir, cj) = build("sig A {}\nrun foo { some r: set A | some r } for 3\n");
    assert_eq!(command_str(&ir, &cj), "($foo_r in A and some $foo_r)");
}

#[test]
fn golden_skolem_marked_arrow() {
    // run foo { some f: A one -> one B | some f } for 3
    // jar dump T9b: some foo_f: set A->B | foo_f in (A->B) and
    //   (all v0 | one(v0.foo_f) and (v0.foo_f) in B) and
    //   (all v1 | one(foo_f.v1) and (foo_f.v1) in A) and some foo_f
    // mettle: same, redundant per-column memberships omitted (divergence e).
    let (ir, cj) = build("sig A {}\nsig B {}\nrun foo { some f: A one -> one B | some f } for 3\n");
    assert_eq!(
        command_str(&ir, &cj),
        "($foo_f in (A -> B) and (all _c0: A | one (_c0 . $foo_f)) \
         and (all _c1: B | one ($foo_f . _c1)) and some $foo_f)"
    );
}

#[test]
fn golden_skolem_check_negated_universal() {
    // assert Inj { all f: A lone -> B | some f } check Inj for 3
    // jar dump T9c: !(all Inj_f: set A->B | (Inj_f in (A->B) and
    //   (all v0:A | (v0.Inj_f) in B) and (all v1:B | lone(Inj_f.v1) and
    //   (Inj_f.v1) in A)) implies some Inj_f)
    // The check's `!` makes the universal `f` an effective existential →
    // skolemizable; the decl-constraint becomes the antecedent (probe T9c). The
    // skolem label is the checked assertion's name `Inj` (mt-047 wired the
    // assert-name label for both HO and FO check skolems) → `$Inj_f`.
    let (ir, cj) =
        build("sig A {}\nsig B {}\nassert Inj { all f: A lone -> B | some f }\ncheck Inj for 3\n");
    assert_eq!(
        command_str(&ir, &cj),
        "!((($Inj_f in (A -> B) and (all _c0: B | lone ($Inj_f . _c0))) => some $Inj_f))"
    );
}

#[test]
fn golden_skolem_run_pred_relational_param() {
    // pred p[r: A -> B] { some r } run p for 3
    // jar dump T9f: some p_r: set A->B | p_r in (A->B) and some p_r
    let (ir, cj) = build("sig A {}\nsig B {}\npred p[r: A -> B] { some r }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "($p_r in (A -> B) and some $p_r)");
}

#[test]
fn golden_skolem_run_pred_set_unary_param() {
    // pred q[s: set A] { some s } run q — a set-marked unary param.
    let (ir, cj) = build("sig A {}\npred q[s: set A] { some s }\nrun q for 3\n");
    assert_eq!(command_str(&ir, &cj), "($q_s in A and some $q_s)");
}

#[test]
fn ho_universal_polarity_defers_typed() {
    // `all r: set A | …` is effective-universal → jar HigherOrderDeclException,
    // mettle `TranslateError::HigherOrder` (probe T9d).
    assert!(matches!(
        try_build("sig A {}\nrun foo { all r: set A | some r } for 3\n"),
        Err(TranslateError::HigherOrder { .. })
    ));
    // A HO existential nested under a universal `all x: A` (probe T9e).
    assert!(matches!(
        try_build("sig A {}\nrun foo { all x: A | some r: set A | x in r } for 3\n"),
        Err(TranslateError::HigherOrder { .. })
    ));
}

// ---------------------------------------------------------------------------
// int-sorted expression in relation position (mt-038 D)
// ---------------------------------------------------------------------------
// `lower_rel`'s entry now mirrors `lower_int`'s existing Rel->AtomToInt guard:
// an int-sorted subexpression (`#e`, an Int-returning call, a `let`-bound int
// value) reaching relation position implicitly casts via `Int[·]`
// (translation-ref §2.1's `IntToAtom` row). Needed because several callers
// always lower through `lower_rel` regardless of the value's real sort: a call
// argument (`bind_call_params`), a `let` binding's value, and a genuinely
// relational `+`/`-` operand. `+`/`-` themselves stay relational union/diff at
// every sortedness (resolution §4.5: "no automatic int<->Int coercion" — `1 +
// 2` is the set `{1,2}`, never `3`) — only the *operand* needs the cast.

#[test]
fn int_operand_of_relational_plus_promotes() {
    // fact { #A = #B + 1 }  run {} for 3
    // jar dump (DumpK2, probe p1, scratchpad/probe/plus/p1.als): the generated
    // Kodkod code builds `x13.union(x15)` (Expression.union, NOT
    // IntExpression.plus) for `#B + 1`, confirming `+` stays relational union
    // even between two int-sorted operands (resolution §4.5) — the jar casts
    // each operand via `Int[·]` first: `Int[#A] = (Int[#B] + Int[1])`. Before
    // this fix, `#B` (a bare `Card` reaching `lower_rel` as a union operand)
    // hit the "unary operator in a relation position" typed defer.
    let (ir, cj) = build("sig A {}\nsig B {}\nfact { #A = #B + 1 }\nrun {} for 3\n");
    assert_eq!(fact_str(&ir, &cj), "Int[#A] = (Int[#B] + Int[1])");
}

#[test]
fn let_bound_int_value_promotes_in_relation_position() {
    // sig A {}  pred p { let t = #A | t > 0 }  run p for 3
    // A `let` binding's value is always lowered via `lower_rel` (unchanged);
    // with the guard, an int-sorted value (`#A`) promotes to `Int[#A]` instead
    // of erroring. `t`'s own later int-position use round-trips through
    // `AtomToInt(IntToAtom(#A))`, which mt-044's `int[Int[x]] == x` peephole
    // (translation-ref §2.4) folds back to `#A` — keeping the accumulated
    // overflow the `Int[·]` boundary would otherwise drop (§11.3).
    let (ir, cj) = build("sig A {}\npred p { let t = #A | t > 0 }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "#A > 0");
}

#[test]
fn int_returning_call_arg_promotes_before_inlining() {
    // sig A {}  pred p { plus[#A, 1] = 2 }  run p for 3
    // `util/integer` is auto-opened into every module (resolution §4.5), so
    // `plus` is reachable unqualified. `bind_call_params` always lowers call
    // arguments via `lower_rel`; before this fix, the bare `#A` argument to
    // `plus[..]` hit the same typed defer as the top-level case.
    assert!(try_build("sig A {}\npred p { plus[#A, 1] = 2 }\nrun p for 3\n").is_ok());
}

// ---------------------------------------------------------------------------
// explicit-receiver call binding (mt-038 D)
// ---------------------------------------------------------------------------
// `bind_call_params` bound a receiver-pred's `this` unconditionally to the
// *caller's own* current `this` (`lookup_binder("this")`), which is only
// correct for an *implicit* receiver (a bare call forwarding an enclosing
// sig's `this`). An *explicit* join-syntax receiver (`ks.iterator[args]`,
// resolution §3.5's box-join sugar for `iterator[ks, args]`) was silently
// dropped: since the `this` branch never consumed from the argument queue,
// every explicit arg shifted one parameter left and the receiver vanished —
// "unbound variable `this`" if the body referenced it, or a silently wrong
// binding (an argument doing double duty as both a real param and the
// never-bound receiver) if it didn't. `CallChoice::args` already carries the
// receiver as `args[0]` whenever `implicit_this` is false (verified empirically
// against `als_types::resolve`'s recorded choices) — `implicit_this` now
// threads through `inline_pred`/`inline_fun`/`inline_fun_int` so the receiver
// is read from there instead of re-derived.

#[test]
fn explicit_receiver_binds_this_from_the_join() {
    // sig A { f: set A }  sig B {}  pred A.foo[x: B] { some this.f }
    // run { some a: A, b: B | a.foo[b] } for 3
    // jar dump (DumpK2, scratchpad/probe/recv/r2.als): `a.foo[b]` inlines to
    // `some (a . A.f)` — `this` bound to the join's LHS `a`, not any ambient
    // `this` (there is none here: the call sits inside a `run` block, not
    // another receiver-pred/appended-fact body). The top-level `some a: A, b: B`
    // are first-order existentials, so each skolemizes to a constant relation
    // (mt-047, §15; anonymous `run` ⇒ bare `$a`/`$b` names): membership + `one`
    // per var, conjoined with the inlined body.
    let (ir, cj) = build(
        "sig A { f: set A }\nsig B {}\npred A.foo[x: B] { some this.f }\n\
         run { some a: A, b: B | a.foo[b] } for 3\n",
    );
    assert_eq!(
        command_str(&ir, &cj),
        "($a in A and one $a and $b in B and one $b and some ($a . A.f))"
    );
}

// ---------------------------------------------------------------------------
// mt-040 (c): `run`/`check` target own-module priority (LEDGER-009, PINNED)
// ---------------------------------------------------------------------------
// A bare `run add` where the user's own module declares `pred add` AND the
// auto-opened `util/integer` exposes `fun add`: the jar resolves the target
// own-module-first (`getRawQS` before `getRawNQS`), so the user's pred is run
// and `util/integer/add` is shadowed (LEDGER-009, jar-verified 2026-07-18:
// `pred add { no A }` with `one sig A` ⟹ UNSAT — the own pred, always false).
// mettle's `lookup_run_target` currently collects candidates from every
// reachable module with no own-module priority, so it sees two `add`s and
// defers typed ("overloaded run target"). Shipping the own-module-first rule is
// a solve-visible candidate choice reserved for owner approval; this test is
// ready to flip when LEDGER-009 is approved and the rule lands.
#[test]
fn run_target_own_module_first() {
    // Own-module `pred add` shadows the auto-opened `util/integer/add`; the
    // command must lower (to the user pred), not defer as overloaded.
    assert!(try_build("one sig A {}\nsig S {}\npred add { no A }\nrun add for 3\n").is_ok());
}
