//! Colocated parser tests: every precedence/associativity rule of grammar-doc
//! section 3, the special dot/bracket targets, and every paragraph shape of
//! section 4. Structure is asserted directly against the AST (the mt-012
//! pretty-printer will add snapshot round-trips later).
//!
//! Test assertions favor `unwrap`/`expect` for brevity; the crate-level deny
//! (STYLE L3) targets library code, and this scoped allow keeps the tests
//! readable without weakening the library lints.
#![allow(clippy::unwrap_used, clippy::expect_used)]

use super::{parse, parse_tokens, ParseError};
use crate::ast::{
    BinOp, CmdKind, CmdTarget, CmpOp, Const, Expr, ExprId, ExprKind, Mult, Para, ParaName, Quant,
    ScopeEnd, ScopeTarget, SigMult, SigParent, UnOp,
};
use crate::span::FileId;
use crate::{cook, lex, ArenaId};

fn ast_of(src: &str) -> crate::ast::Ast {
    match parse(src, FileId::from_index(0)) {
        Ok(ast) => ast,
        Err(e) => panic!("expected {src:?} to parse, got {e:?}"),
    }
}

fn err_of(src: &str) -> ParseError {
    match parse(src, FileId::from_index(0)) {
        Ok(_) => panic!("expected {src:?} to fail parsing"),
        Err(e) => e,
    }
}

/// Parses `run { <src> }` and returns the single block formula.
fn expr_ast(src: &str) -> (crate::ast::Ast, ExprId) {
    let ast = ast_of(&format!("run {{ {src} }}"));
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected a command");
    };
    let CmdTarget::Block(block) = cmd.target else {
        panic!("expected a block target");
    };
    let ExprKind::Block(forms) = &ast.exprs[block].kind else {
        panic!("expected a block");
    };
    assert_eq!(forms.len(), 1, "expected exactly one formula in {src:?}");
    let id = forms[0];
    (ast, id)
}

fn kind(ast: &crate::ast::Ast, id: ExprId) -> ExprKind {
    ast.exprs[id].kind.clone()
}

fn expr(ast: &crate::ast::Ast, id: ExprId) -> Expr {
    ast.exprs[id].clone()
}

fn name_text(ast: &crate::ast::Ast, id: ExprId) -> String {
    let ExprKind::Name(q) = &ast.exprs[id].kind else {
        panic!("expected a name, got {:?}", ast.exprs[id].kind);
    };
    q.segments
        .iter()
        .map(|s| s.text.as_str())
        .collect::<Vec<_>>()
        .join("/")
}

// -- Precedence & associativity (section 3) -------------------------------

#[test]
fn or_is_left_associative() {
    let (a, id) = expr_ast("p || q || r");
    // (p || q) || r
    let ExprKind::Binary {
        op: BinOp::Or, lhs, ..
    } = kind(&a, id)
    else {
        panic!("expected top-level or");
    };
    assert!(matches!(
        kind(&a, lhs),
        ExprKind::Binary { op: BinOp::Or, .. }
    ));
}

#[test]
fn implies_is_right_associative() {
    let (a, id) = expr_ast("p => q => r");
    // p => (q => r)
    let ExprKind::Binary {
        op: BinOp::Implies,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected implies");
    };
    assert!(matches!(
        kind(&a, rhs),
        ExprKind::Binary {
            op: BinOp::Implies,
            ..
        }
    ));
}

#[test]
fn and_is_left_associative() {
    let (a, id) = expr_ast("p && q && r");
    let ExprKind::Binary {
        op: BinOp::And,
        lhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected and");
    };
    assert!(matches!(
        kind(&a, lhs),
        ExprKind::Binary { op: BinOp::And, .. }
    ));
}

#[test]
fn plus_is_left_associative() {
    let (a, id) = expr_ast("x + y + z");
    let ExprKind::Binary {
        op: BinOp::Union,
        lhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected union");
    };
    assert!(matches!(
        kind(&a, lhs),
        ExprKind::Binary {
            op: BinOp::Union,
            ..
        }
    ));
}

#[test]
fn comparison_chaining_is_left_associative() {
    // a = b = c  ==  (a = b) = c
    let (a, id) = expr_ast("p = q = r");
    let ExprKind::Compare {
        op: CmpOp::Eq, lhs, ..
    } = kind(&a, id)
    else {
        panic!("expected compare");
    };
    assert!(matches!(
        kind(&a, lhs),
        ExprKind::Compare { op: CmpOp::Eq, .. }
    ));
}

#[test]
fn arrow_is_right_associative() {
    // A -> B -> C  ==  A -> (B -> C)
    let (a, id) = expr_ast("A -> B -> C");
    let ExprKind::Arrow { rhs, .. } = kind(&a, id) else {
        panic!("expected arrow");
    };
    assert!(matches!(kind(&a, rhs), ExprKind::Arrow { .. }));
}

#[test]
fn all_sixteen_arrow_multiplicities() {
    let mults = ["set", "some", "one", "lone"];
    for l in mults {
        for r in mults {
            let src = format!("A {l} -> {r} B");
            let (a, id) = expr_ast(&src);
            let ExprKind::Arrow {
                lhs_mult, rhs_mult, ..
            } = kind(&a, id)
            else {
                panic!("expected arrow for {src:?}");
            };
            let want = |m: &str| match m {
                "some" => Some(Mult::Some),
                "one" => Some(Mult::One),
                "lone" => Some(Mult::Lone),
                _ => None, // set == unannotated
            };
            assert_eq!(lhs_mult, want(l), "lhs of {src:?}");
            assert_eq!(rhs_mult, want(r), "rhs of {src:?}");
        }
    }
}

#[test]
fn not_is_looser_than_comparison() {
    // !a = b  ==  !(a = b)
    let (a, id) = expr_ast("!p = q");
    assert!(matches!(
        kind(&a, id),
        ExprKind::Unary { op: UnOp::Not, .. }
    ));
    let ExprKind::Unary { expr, .. } = kind(&a, id) else {
        unreachable!()
    };
    assert!(matches!(kind(&a, expr), ExprKind::Compare { .. }));
}

#[test]
fn set_test_is_tighter_than_comparison() {
    // no a = b  ==  (no a) = b
    let (a, id) = expr_ast("no p = q");
    let ExprKind::Compare {
        op: CmpOp::Eq, lhs, ..
    } = kind(&a, id)
    else {
        panic!("expected compare at top");
    };
    assert!(matches!(
        kind(&a, lhs),
        ExprKind::Unary { op: UnOp::No, .. }
    ));
}

#[test]
fn cardinality_is_tighter_than_plus() {
    // #a + b  ==  (#a) + b
    let (a, id) = expr_ast("#p + q");
    let ExprKind::Binary {
        op: BinOp::Union,
        lhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected union at top");
    };
    assert!(matches!(
        kind(&a, lhs),
        ExprKind::Unary { op: UnOp::Card, .. }
    ));
}

// -- Binder as rightmost operand (section 3.1) ----------------------------

#[test]
fn quantifier_as_rightmost_operand_of_plus() {
    // a + sum x: A | f[x]
    let (a, id) = expr_ast("y + sum x: A | f[x]");
    let ExprKind::Binary {
        op: BinOp::Union,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected union");
    };
    assert!(matches!(
        kind(&a, rhs),
        ExprKind::Quant {
            quant: Quant::Sum,
            ..
        }
    ));
}

#[test]
fn let_as_rightmost_operand_of_and() {
    // a && let y = e | b
    let (a, id) = expr_ast("p && let y = univ | q");
    let ExprKind::Binary {
        op: BinOp::And,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected and");
    };
    assert!(matches!(kind(&a, rhs), ExprKind::Let { .. }));
}

// -- Dangling else --------------------------------------------------------

#[test]
fn dangling_else_binds_nearest() {
    // a => b => c else d  ==  a => (b => c else d)
    let (a, id) = expr_ast("p => q => r else s");
    let ExprKind::Binary {
        op: BinOp::Implies,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected implies at top");
    };
    assert!(matches!(kind(&a, rhs), ExprKind::IfThenElse { .. }));
}

// -- Dot / bracket / prime / closure (sections 3, 19-20) ------------------

#[test]
fn box_and_dot_interleave_left() {
    // a.b[c]  ==  (a.b)[c]
    let (a, id) = expr_ast("a.b[c]");
    let ExprKind::BoxJoin { target, .. } = kind(&a, id) else {
        panic!("expected box join at top");
    };
    assert!(matches!(
        kind(&a, target),
        ExprKind::Binary {
            op: BinOp::Join,
            ..
        }
    ));
    // a[c].b  ==  (a[c]).b
    let (a, id) = expr_ast("a[c].b");
    let ExprKind::Binary {
        op: BinOp::Join,
        lhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected join at top");
    };
    assert!(matches!(kind(&a, lhs), ExprKind::BoxJoin { .. }));
}

#[test]
fn dot_transpose_right_operand() {
    // a.~r
    let (a, id) = expr_ast("a.~r");
    let ExprKind::Binary {
        op: BinOp::Join,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected join");
    };
    assert!(matches!(
        kind(&a, rhs),
        ExprKind::Unary {
            op: UnOp::Transpose,
            ..
        }
    ));
}

#[test]
fn prime_binds_tighter_than_dot() {
    // a.b'  ==  a.(b')
    let (a, id) = expr_ast("a.b'");
    let ExprKind::Binary {
        op: BinOp::Join,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected join");
    };
    assert!(matches!(
        kind(&a, rhs),
        ExprKind::Unary {
            op: UnOp::Prime,
            ..
        }
    ));
}

#[test]
fn closure_binds_tighter_than_prime() {
    // ~a'  ==  (~a)'
    let (a, id) = expr_ast("~a'");
    let ExprKind::Unary {
        op: UnOp::Prime,
        expr,
    } = kind(&a, id)
    else {
        panic!("expected prime at top");
    };
    assert!(matches!(
        kind(&a, expr),
        ExprKind::Unary {
            op: UnOp::Transpose,
            ..
        }
    ));
}

// -- Int casts, sum, prefixes vs quantifier -------------------------------

#[test]
fn int_and_sum_prefix_casts() {
    let (a, id) = expr_ast("int p");
    assert!(matches!(
        kind(&a, id),
        ExprKind::Unary {
            op: UnOp::IntOf,
            ..
        }
    ));
    let (a, id) = expr_ast("sum p");
    assert!(matches!(
        kind(&a, id),
        ExprKind::Unary {
            op: UnOp::SumOf,
            ..
        }
    ));
    // sum x: A | e is a quantifier, not a cast.
    let (a, id) = expr_ast("sum x: A | int x");
    assert!(matches!(
        kind(&a, id),
        ExprKind::Quant {
            quant: Quant::Sum,
            ..
        }
    ));
}

// -- Special dot/bracket targets (section 3.2) ----------------------------

#[test]
fn builtin_bracket_targets() {
    for (src, want) in [
        ("disj[a, b]", "disj"),
        ("pred/totalOrder[a, b]", "pred/totalOrder"),
        ("int[e]", "int"),
        ("sum[e]", "sum"),
    ] {
        let (a, id) = expr_ast(src);
        let ExprKind::BoxJoin { target, args } = kind(&a, id) else {
            panic!("expected box join for {src:?}");
        };
        assert_eq!(name_text(&a, target), want, "target of {src:?}");
        assert!(!args.is_empty());
    }
}

#[test]
fn builtin_dot_targets() {
    for (src, want) in [("a.disj", "disj"), ("a.int", "int"), ("a.sum", "sum")] {
        let (a, id) = expr_ast(src);
        let ExprKind::Binary {
            op: BinOp::Join,
            rhs,
            ..
        } = kind(&a, id)
        else {
            panic!("expected join for {src:?}");
        };
        assert_eq!(name_text(&a, rhs), want);
    }
}

#[test]
fn empty_box_is_just_the_target() {
    // f[] == f
    let (a, id) = expr_ast("f[]");
    assert_eq!(name_text(&a, id), "f");
}

#[test]
fn fun_infix_and_atom() {
    // fun/add infix operator
    let (a, id) = expr_ast("x fun/add y");
    assert!(matches!(
        kind(&a, id),
        ExprKind::Binary {
            op: BinOp::IntAdd,
            ..
        }
    ));
    // fun/min atom
    let (a, id) = expr_ast("fun/min");
    assert_eq!(name_text(&a, id), "fun/min");
}

// -- Negative-literal folding (section 2 F3) ------------------------------

#[test]
fn negative_literal_folds_after_operator() {
    // x = -1  →  Num(-1)
    let (a, id) = expr_ast("x = -1");
    let ExprKind::Compare { rhs, .. } = kind(&a, id) else {
        panic!("expected compare");
    };
    assert!(matches!(kind(&a, rhs), ExprKind::Num(-1)));
}

#[test]
fn minus_after_expression_is_difference() {
    // n - 1  →  Diff(n, 1)
    let (a, id) = expr_ast("n - 1");
    let ExprKind::Binary {
        op: BinOp::Diff,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected difference");
    };
    assert!(matches!(kind(&a, rhs), ExprKind::Num(1)));
}

// -- Qualified names & builtins -------------------------------------------

#[test]
fn qualified_names() {
    let (a, id) = expr_ast("a/b/c");
    assert_eq!(name_text(&a, id), "a/b/c");
    let (a, id) = expr_ast("this/x");
    assert_eq!(name_text(&a, id), "this/x");
    let (a, id) = expr_ast("seq/Int");
    assert_eq!(name_text(&a, id), "seq/Int");
}

#[test]
fn builtin_constants_and_names() {
    let (a, id) = expr_ast("iden");
    assert!(matches!(kind(&a, id), ExprKind::Const(Const::Iden)));
    let (a, id) = expr_ast("univ");
    assert!(matches!(kind(&a, id), ExprKind::Const(Const::Univ)));
    let (a, id) = expr_ast("none");
    assert!(matches!(kind(&a, id), ExprKind::Const(Const::None)));
    let (a, id) = expr_ast("this");
    assert!(matches!(kind(&a, id), ExprKind::This));
    let (a, id) = expr_ast("Int");
    assert_eq!(name_text(&a, id), "Int");
}

#[test]
fn at_name_suppresses_this() {
    let (a, id) = expr_ast("@f");
    let ExprKind::AtName(q) = kind(&a, id) else {
        panic!("expected @name");
    };
    assert_eq!(q.segments[0].text, "f");
}

// -- Comprehensions & blocks ----------------------------------------------

#[test]
fn comprehension_with_and_without_body() {
    let (a, id) = expr_ast("{ x: A | p }");
    let ExprKind::Comprehension { decls, body } = kind(&a, id) else {
        panic!("expected comprehension");
    };
    assert_eq!(decls.len(), 1);
    assert!(!matches!(kind(&a, body), ExprKind::Block(v) if v.is_empty()));
    // Omitted body defaults to true (empty block).
    let (a, id) = expr_ast("{ x: A }");
    let ExprKind::Comprehension { body, .. } = kind(&a, id) else {
        panic!("expected comprehension");
    };
    assert!(matches!(kind(&a, body), ExprKind::Block(v) if v.is_empty()));
}

#[test]
fn block_vs_comprehension_disambiguation() {
    // `{ some x: A | p }` is a block containing a quantifier formula.
    let (a, id) = expr_ast("{ some x: A | p }");
    let ExprKind::Block(forms) = kind(&a, id) else {
        panic!("expected a block, got {:?}", kind(&a, id));
    };
    assert_eq!(forms.len(), 1);
    assert!(matches!(kind(&a, forms[0]), ExprKind::Quant { .. }));
    // Empty block is true.
    let (a, id) = expr_ast("{}");
    assert!(matches!(kind(&a, id), ExprKind::Block(v) if v.is_empty()));
}

#[test]
fn semicolon_sequencing() {
    let (a, id) = expr_ast("p ; q");
    assert!(matches!(
        kind(&a, id),
        ExprKind::Binary { op: BinOp::Seq, .. }
    ));
}

// -- Multiplicity conversion in bounds (section 4.4) ----------------------

#[test]
fn decl_bound_multiplicity_conversion() {
    let ast = ast_of("sig S { f: one A, g: set B, h: lone C, i: some D }");
    let Para::Sig(sig) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected sig");
    };
    let ops: Vec<UnOp> = sig
        .fields
        .iter()
        .map(|d| {
            let bound = ast.decls[*d].bound;
            match &ast.exprs[bound].kind {
                ExprKind::Unary { op, .. } => *op,
                other => panic!("expected unary bound, got {other:?}"),
            }
        })
        .collect();
    assert_eq!(
        ops,
        vec![UnOp::OneOf, UnOp::SetOf, UnOp::LoneOf, UnOp::SomeOf]
    );
}

#[test]
fn fun_return_multiplicity_conversion() {
    let ast = ast_of("fun f: one A { A }");
    let Para::Fun(fun) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected fun");
    };
    assert!(matches!(
        ast.exprs[fun.returns].kind,
        ExprKind::Unary {
            op: UnOp::OneOf,
            ..
        }
    ));
}

// -- Declarations: disj positions, defined fields -------------------------

#[test]
fn disj_both_positions_and_defined_field() {
    let ast = ast_of("sig S { disj a, b: disj A, c = A }");
    let Para::Sig(sig) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected sig");
    };
    let d0 = &ast.decls[sig.fields[0]];
    assert!(d0.is_disj && d0.is_bound_disj);
    assert_eq!(d0.names.len(), 2);
    let d1 = &ast.decls[sig.fields[1]];
    assert!(matches!(
        ast.exprs[d1.bound].kind,
        ExprKind::Unary {
            op: UnOp::ExactlyOf,
            ..
        }
    ));
}

#[test]
fn defined_disjoint_field_is_error() {
    assert!(matches!(
        err_of("sig S { disj a, b = A }"),
        ParseError::DefinedFieldDisjoint { .. }
    ));
}

// -- Paragraph forms (section 4) ------------------------------------------

#[test]
fn sig_qualifiers_and_parents() {
    let ast = ast_of("abstract var one sig A extends P {}");
    let Para::Sig(sig) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected sig");
    };
    assert!(sig.qual.is_abstract && sig.qual.is_var);
    assert_eq!(sig.qual.mult, Some(SigMult::One));
    assert!(matches!(sig.parent, SigParent::Extends(_)));

    let ast = ast_of("sig A in P + Q {}");
    let Para::Sig(sig) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected sig");
    };
    let SigParent::In(refs) = &sig.parent else {
        panic!("expected in-parent");
    };
    assert_eq!(refs.len(), 2);

    let ast = ast_of("sig A = P + Q {}");
    let Para::Sig(sig) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected sig");
    };
    assert!(matches!(sig.parent, SigParent::Eq(_)));
}

#[test]
fn sig_with_appended_fact_and_multiple_names() {
    let ast = ast_of("sig A, B, C {} { some this }");
    let Para::Sig(sig) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected sig");
    };
    assert_eq!(sig.names.len(), 3);
    assert!(sig.fact.is_some());
}

#[test]
fn duplicate_sig_qualifier_is_error() {
    assert!(matches!(
        err_of("abstract abstract sig A {}"),
        ParseError::DuplicateSigQual { .. }
    ));
}

#[test]
fn enum_and_empty_enum() {
    let ast = ast_of("enum Color { Red, Green, Blue }");
    let Para::Enum(e) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected enum");
    };
    assert_eq!(e.variants.len(), 3);
    assert!(matches!(
        err_of("enum Empty {}"),
        ParseError::EmptyEnum { .. }
    ));
}

#[test]
fn fact_and_assert_names() {
    let ast = ast_of("fact named { p }");
    assert!(matches!(
        &ast.paras[ast.paragraphs[0]],
        Para::Fact(f) if matches!(&f.name, Some(ParaName::Ident(i)) if i.text == "named")
    ));
    let ast = ast_of("fact \"a string name\" { p }");
    assert!(matches!(
        &ast.paras[ast.paragraphs[0]],
        Para::Fact(f) if matches!(&f.name, Some(ParaName::Str { value, .. }) if value == "a string name")
    ));
    let ast = ast_of("assert A { p }");
    assert!(matches!(&ast.paras[ast.paragraphs[0]], Para::Assert(_)));
    // Anonymous fact.
    let ast = ast_of("fact { p }");
    assert!(matches!(
        &ast.paras[ast.paragraphs[0]],
        Para::Fact(f) if f.name.is_none()
    ));
}

#[test]
fn pred_and_fun_receiver_and_params() {
    let ast = ast_of("pred A.p[x: A, y: B] { x = y }");
    let Para::Pred(pred) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected pred");
    };
    assert!(pred.receiver.is_some());
    assert_eq!(pred.params.len(), 2);

    // Paren params and no params.
    let ast = ast_of("pred q(x: A) {}");
    let Para::Pred(pred) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected pred");
    };
    assert_eq!(pred.params.len(), 1);
    let ast = ast_of("pred r {}");
    let Para::Pred(pred) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected pred");
    };
    assert!(pred.params.is_empty());

    let ast = ast_of("fun f[x: A]: B { x.r }");
    assert!(matches!(&ast.paras[ast.paragraphs[0]], Para::Fun(_)));
}

#[test]
fn macros_with_both_bodies_and_param_forms() {
    let ast = ast_of("let m = univ");
    assert!(matches!(&ast.paras[ast.paragraphs[0]], Para::Macro(_)));
    let ast = ast_of("let m[a, b] = a + b");
    let Para::Macro(mac) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected macro");
    };
    assert_eq!(mac.params.len(), 2);
    let ast = ast_of("let m(a) { some a }");
    let Para::Macro(mac) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected macro");
    };
    assert_eq!(mac.params.len(), 1);
    // Empty param list.
    let ast = ast_of("let m[] = univ");
    let Para::Macro(mac) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected macro");
    };
    assert!(mac.params.is_empty());
}

#[test]
fn module_header_and_opens() {
    let ast = ast_of("module foo/bar[X, exactly Y]\nopen util/ordering[A] as ord");
    let header = ast.header.expect("expected module header");
    assert_eq!(header.name.segments.len(), 2);
    assert_eq!(header.params.len(), 2);
    assert!(header.params[1].is_exact);
    assert_eq!(ast.opens.len(), 1);
    assert_eq!(ast.opens[0].alias.as_ref().unwrap().text, "ord");
}

#[test]
fn module_header_not_first_is_error() {
    assert!(matches!(
        err_of("sig A {}\nmodule late"),
        ParseError::ModuleHeaderNotFirst { .. }
    ));
}

#[test]
fn private_paragraphs() {
    let ast = ast_of("private sig A {}");
    let Para::Sig(sig) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected sig");
    };
    assert!(sig.qual.is_private);
    let ast = ast_of("private pred p {}");
    let Para::Pred(pred) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected pred");
    };
    assert!(pred.is_private);
    let ast = ast_of("private open m");
    assert!(ast.opens[0].is_private);
}

// -- Commands & scopes (section 4.5) --------------------------------------

#[test]
fn command_label_reorder_and_targets() {
    // Label via F1.
    let ast = ast_of("c: run p");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected command");
    };
    assert_eq!(cmd.label.as_ref().unwrap().text, "c");
    assert!(matches!(cmd.kind, CmdKind::Run));
    assert!(matches!(&cmd.target, CmdTarget::Name(_)));

    // Block target, no label.
    let ast = ast_of("check { p }");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected command");
    };
    assert!(cmd.label.is_none());
    assert!(matches!(cmd.kind, CmdKind::Check));
    assert!(matches!(&cmd.target, CmdTarget::Block(_)));
}

#[test]
fn command_followup_chaining() {
    let ast = ast_of("run p => check q");
    assert_eq!(ast.paragraphs.len(), 2);
    let Para::Cmd(first) = &ast.paras[ast.paragraphs[0]] else {
        panic!();
    };
    let Para::Cmd(second) = &ast.paras[ast.paragraphs[1]] else {
        panic!();
    };
    assert!(!first.is_followup);
    assert!(second.is_followup);
}

#[test]
fn scope_forms() {
    // Default only.
    let ast = ast_of("run p for 3");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!();
    };
    let scope = cmd.scope.as_ref().unwrap();
    assert_eq!(scope.default, Some(3));
    assert!(scope.entries.is_empty());

    // Default + but-list with exactly and ranges.
    let ast = ast_of("run p for 3 but exactly 2 A, 1..4 steps, 4 int, 5 seq, 2 String");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!();
    };
    let scope = cmd.scope.as_ref().unwrap();
    assert_eq!(scope.default, Some(3));
    assert_eq!(scope.entries.len(), 5);
    assert!(scope.entries[0].is_exact);
    assert!(matches!(scope.entries[0].target, ScopeTarget::Sig(_)));
    assert!(matches!(scope.entries[1].target, ScopeTarget::Steps));
    assert!(matches!(scope.entries[1].end, ScopeEnd::Bounded(4)));
    assert!(matches!(scope.entries[2].target, ScopeTarget::Int));
    assert!(matches!(scope.entries[3].target, ScopeTarget::Seq));
    assert!(matches!(scope.entries[4].target, ScopeTarget::Str));

    // Entries-only form (no default).
    let ast = ast_of("run p for 2 A, 3 B");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!();
    };
    let scope = cmd.scope.as_ref().unwrap();
    assert_eq!(scope.default, None);
    assert_eq!(scope.entries.len(), 2);
}

#[test]
fn scope_range_and_expect() {
    let ast = ast_of("run p for exactly 3 A expect 1");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!();
    };
    assert!(matches!(cmd.expect, Some(crate::ast::Expect::Sat)));

    let ast = ast_of("check q for 3 but 2..5 B expect 0");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!();
    };
    assert!(matches!(cmd.expect, Some(crate::ast::Expect::Unsat)));
    assert!(matches!(
        cmd.scope.as_ref().unwrap().entries[0].end,
        ScopeEnd::Bounded(5)
    ));
}

#[test]
fn scope_on_univ_and_none_are_errors() {
    assert!(matches!(
        err_of("run p for 3 univ"),
        ParseError::ScopeOnUniv { .. }
    ));
    assert!(matches!(
        err_of("run p for 3 none"),
        ParseError::ScopeOnNone { .. }
    ));
}

#[test]
fn growing_and_exactly_int_scope_errors() {
    assert!(matches!(
        err_of("run p for 1..4 int"),
        ParseError::GrowingScope { .. }
    ));
    assert!(matches!(
        err_of("run p for exactly 4 Int"),
        ParseError::ExactlyRedundant { .. }
    ));
}

// -- Declared-name hygiene ------------------------------------------------

#[test]
fn dollar_in_declared_name_is_error() {
    assert!(matches!(
        err_of("sig A$B {}"),
        ParseError::DollarInName { .. }
    ));
}

#[test]
fn let_name_with_slash_is_error() {
    assert!(matches!(
        err_of("run { let a/b = univ | p }"),
        ParseError::LetNameSlash { .. }
    ));
}

// -- Spans cover exactly the source (STYLE G1) ----------------------------

#[test]
fn spans_cover_source() {
    // `a + b` — the union node spans the whole "a + b".
    let (a, id) = expr_ast("a + b");
    let e = expr(&a, id);
    // Inside `run { a + b }`, "a + b" starts at byte 6.
    assert_eq!((e.span.start, e.span.end), (6, 11));

    // A qualified name spans exactly its text.
    let (a, id) = expr_ast("foo/bar");
    let e = expr(&a, id);
    assert_eq!((e.span.start, e.span.end), (6, 13));

    // A number literal.
    let (a, id) = expr_ast("42");
    assert_eq!(kind(&a, id), ExprKind::Num(42));
    let e = expr(&a, id);
    assert_eq!((e.span.start, e.span.end), (6, 8));
}

// -- Lower-level entry point ----------------------------------------------

#[test]
fn parse_tokens_matches_parse() {
    let src = "sig A {}";
    let toks = cook(&lex(src, FileId::from_index(0)).unwrap(), src);
    let ast = parse_tokens(toks, src).expect("parse_tokens");
    assert_eq!(ast.paragraphs.len(), 1);
}

// -- `;` sequencing shape (reference SuperP / SuperOrBar) ------------------

/// `{ a ; b c }` — the WHOLE remaining block conjoins under the Seq's rhs:
/// `Block([Seq(a, Block([b, c]))])` (jar semantics: `a && after (b && c)`).
#[test]
fn block_seq_captures_whole_remainder() {
    let (a, id) = expr_ast("p ; q r");
    let ExprKind::Binary {
        op: BinOp::Seq,
        lhs,
        rhs,
    } = kind(&a, id)
    else {
        panic!("expected Seq as the single block formula");
    };
    assert_eq!(name_text(&a, lhs), "p");
    let ExprKind::Block(rest) = kind(&a, rhs) else {
        panic!("expected the remainder conjoined as a Block");
    };
    assert_eq!(rest.len(), 2);
    assert_eq!(name_text(&a, rest[0]), "q");
    assert_eq!(name_text(&a, rest[1]), "r");
}

/// `{ a ; b ; c }` — nested Seqs stay right-nested: `Seq(a, Seq(b, c))`.
#[test]
fn block_seq_nests_right() {
    let (a, id) = expr_ast("p ; q ; r");
    let ExprKind::Binary {
        op: BinOp::Seq,
        lhs,
        rhs,
    } = kind(&a, id)
    else {
        panic!("expected outer Seq");
    };
    assert_eq!(name_text(&a, lhs), "p");
    let ExprKind::Binary {
        op: BinOp::Seq,
        lhs: inner_lhs,
        rhs: inner_rhs,
    } = kind(&a, rhs)
    else {
        panic!("expected inner Seq");
    };
    assert_eq!(name_text(&a, inner_lhs), "q");
    assert_eq!(name_text(&a, inner_rhs), "r");
}

/// `all x: A | p ; q` — the quantifier-body `;` takes the remaining
/// EXPRESSION (here exactly `q`) as its rhs (`SuperOrBar ::= BAR ExprNoSeq
/// TRCSEQ Expr`).
#[test]
fn quant_body_seq_rhs_is_expression() {
    let (a, id) = expr_ast("all x: A | p ; q");
    let ExprKind::Quant { body, .. } = kind(&a, id) else {
        panic!("expected quantifier");
    };
    let ExprKind::Binary {
        op: BinOp::Seq,
        lhs,
        rhs,
    } = kind(&a, body)
    else {
        panic!("expected Seq body");
    };
    assert_eq!(name_text(&a, lhs), "p");
    assert_eq!(name_text(&a, rhs), "q");
}

/// Parens confine a `;`: `{ (p ; q) r }` is two block formulas, the first a
/// Seq whose rhs is exactly `q`.
#[test]
fn parenthesized_seq_is_confined() {
    let ast = ast_of("run { (p ; q) r }");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected command");
    };
    let CmdTarget::Block(block) = cmd.target else {
        panic!("expected block target");
    };
    let ExprKind::Block(forms) = &ast.exprs[block].kind else {
        panic!("expected block");
    };
    assert_eq!(forms.len(), 2);
    let ExprKind::Binary {
        op: BinOp::Seq,
        rhs,
        ..
    } = kind(&ast, forms[0])
    else {
        panic!("expected Seq as first formula");
    };
    assert_eq!(name_text(&ast, rhs), "q");
    assert_eq!(name_text(&ast, forms[1]), "r");
}

// -- expect carries any integer --------------------------------------------

#[test]
fn expect_other_integer() {
    let ast = ast_of("run p expect 2");
    let Para::Cmd(cmd) = &ast.paras[ast.paragraphs[0]] else {
        panic!("expected command");
    };
    assert_eq!(cmd.expect, Some(crate::ast::Expect::Other(2)));
}

// -- Prefix tier gating (jar-verified 2026-07-15) ---------------------------

/// Loose prefixes cannot open tight operands — all five jar-rejected.
#[test]
fn loose_prefix_in_tight_operand_rejected() {
    for src in [
        "run { a & !b }",
        "run { a + no b }",
        "run { no !a }",
        "run { # no a }",
        "run { a -> !b }",
    ] {
        assert!(
            matches!(err_of(src), ParseError::Expected { .. }),
            "expected {src:?} to be rejected"
        );
    }
}

/// The gate must not over-reject — all jar-accepted.
#[test]
fn prefix_tier_gate_accepts_valid_shapes() {
    // Binders are exempt at every level.
    let (a, id) = expr_ast("a & all x: X | p");
    let ExprKind::Binary {
        op: BinOp::Intersect,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected intersect");
    };
    assert!(matches!(kind(&a, rhs), ExprKind::Quant { .. }));

    // `=>` rhs is loose enough for `!`.
    let (a, id) = expr_ast("a => !b");
    let ExprKind::Binary {
        op: BinOp::Implies,
        rhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected implies");
    };
    assert!(matches!(
        kind(&a, rhs),
        ExprKind::Unary { op: UnOp::Not, .. }
    ));

    // `!` may nest under itself, and a set test may nest under `!`.
    let (a, id) = expr_ast("!!a");
    let ExprKind::Unary {
        op: UnOp::Not,
        expr: inner,
    } = kind(&a, id)
    else {
        panic!("expected not");
    };
    assert!(matches!(
        kind(&a, inner),
        ExprKind::Unary { op: UnOp::Not, .. }
    ));
    let (a, id) = expr_ast("! no a");
    let ExprKind::Unary {
        op: UnOp::Not,
        expr: inner,
    } = kind(&a, id)
    else {
        panic!("expected not");
    };
    assert!(matches!(
        kind(&a, inner),
        ExprKind::Unary { op: UnOp::No, .. }
    ));

    // `no a + b` == no (a + b): the test's operand spans the union.
    let (a, id) = expr_ast("no a + b");
    let ExprKind::Unary {
        op: UnOp::No,
        expr: inner,
    } = kind(&a, id)
    else {
        panic!("expected no at top");
    };
    assert!(matches!(
        kind(&a, inner),
        ExprKind::Binary {
            op: BinOp::Union,
            ..
        }
    ));

    // `#a + b` == (#a) + b: `#` binds tighter than `+`.
    let (a, id) = expr_ast("#a + b");
    let ExprKind::Binary {
        op: BinOp::Union,
        lhs,
        ..
    } = kind(&a, id)
    else {
        panic!("expected union at top");
    };
    assert!(matches!(
        kind(&a, lhs),
        ExprKind::Unary { op: UnOp::Card, .. }
    ));
}
