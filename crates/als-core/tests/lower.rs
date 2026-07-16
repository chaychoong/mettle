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
    let scoped = compute_universe(&world, &world.commands[0]).expect("universe");
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
    let scoped = compute_universe(&world, &world.commands[0]).expect("universe");
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
    // jar: the negated assertion body (SAT = counterexample).
    let (ir, cj) = build(
        "sig A { f: set A }\nassert noSelf { all a: A | a not in a.f }\ncheck noSelf for 3\n",
    );
    assert_eq!(command_str(&ir, &cj), "!((all a: A | !(a in (a . A.f))))");
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
    // run p where p[x: A] — the param is existentially quantified over A.
    let (ir, cj) = build("sig A { f: set A }\npred p[x: A] { some x.f }\nrun p for 3\n");
    assert_eq!(command_str(&ir, &cj), "(some x: A | some (x . A.f))");
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
    assert_eq!(
        command_str(&ir, &cj),
        "((some iden and some univ) and no none)"
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
fn string_literal_defers() {
    let e = try_build("sig A { s: one String }\npred p { all a: A | a.s = \"x\" }\nrun p for 3\n")
        .unwrap_err();
    assert!(
        matches!(
            e,
            TranslateError::StringUnsupported { .. } | TranslateError::LoweringUnsupported { .. }
        ),
        "{e:?}"
    );
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
