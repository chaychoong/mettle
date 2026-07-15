//! Colocated pretty-printer tests: `insta` snapshots pinning the exact
//! minimal-paren rendering of every construct family, plus a `rt` round-trip
//! harness (parse → print → reparse → dump-equal + idempotent) that is the
//! per-case mirror of `tests/corpus_roundtrip.rs`.
//!
//! Tests favor `unwrap`/`expect` for brevity; the crate-level deny (STYLE L3)
//! targets library code, and this scoped allow keeps the tests readable.
#![allow(clippy::unwrap_used, clippy::expect_used)]

use crate::print::pretty_to_string;
use crate::span::FileId;
use crate::{dump, parse, ArenaId};

fn file() -> FileId {
    FileId::from_index(0)
}

/// Parses `src`, prints it, re-parses the printed text, and asserts the two
/// ASTs are structurally identical (dump-equal) and that printing is
/// idempotent (print∘parse∘print = print).
fn rt(src: &str) -> String {
    let ast1 = match parse(src, file()) {
        Ok(a) => a,
        Err(e) => panic!("expected {src:?} to parse, got {e:?}"),
    };
    let printed1 = pretty_to_string(&ast1);
    let ast2 = match parse(&printed1, file()) {
        Ok(a) => a,
        Err(e) => panic!("re-parse of printed {src:?} failed: {e:?}\n--- printed ---\n{printed1}"),
    };
    let (d1, d2) = (dump(&ast1), dump(&ast2));
    assert_eq!(
        d1, d2,
        "structural mismatch for {src:?}\n--- printed ---\n{printed1}"
    );
    let printed2 = pretty_to_string(&ast2);
    assert_eq!(
        printed1, printed2,
        "printing is not idempotent for {src:?}\n--- first ---\n{printed1}\n--- second ---\n{printed2}"
    );
    printed1
}

/// Round-trips one expression by wrapping it in `run { … }`.
fn rt_expr(expr: &str) -> String {
    rt(&format!("run {{ {expr} }}"))
}

// -- Precedence: parens are added exactly where needed --------------------

#[test]
fn left_assoc_needs_right_parens_only() {
    // (a + b) + c keeps the left child bare; a + (b + c) parenthesizes right.
    assert!(rt_expr("a + b + c").contains("a + b + c"));
    assert!(rt_expr("a + (b + c)").contains("a + (b + c)"));
}

#[test]
fn right_assoc_arrow_needs_left_parens_only() {
    assert!(rt_expr("a -> b -> c").contains("a -> b -> c"));
    assert!(rt_expr("(a -> b) -> c").contains("(a -> b) -> c"));
}

#[test]
fn implies_right_assoc_and_dangling_else() {
    // p => q => r stays bare (right-assoc); the else binds to the inner =>.
    assert!(rt_expr("p => q => r").contains("p => q => r"));
    // A then-branch that is a bare implies must be parenthesized so the else
    // does not migrate inward.
    let s = rt_expr("p => (q => r) else t");
    assert!(s.contains("p => (q => r) else t"), "got: {s}");
}

#[test]
fn tighter_child_drops_parens() {
    // & binds tighter than +, so no parens needed around the &.
    assert!(rt_expr("a + b & c").contains("a + b & c"));
    // + inside & must be parenthesized.
    assert!(rt_expr("(a + b) & c").contains("(a + b) & c"));
}

#[test]
fn prefix_tier_gate_forces_parens() {
    // `no` (comparison tier) cannot open `+`'s right operand bare, so a
    // `+ (no b)` AST must reprint with parens.
    assert!(rt_expr("a + (no b)").contains("a + (no b)"));
    // But `no a = b` is (no a) = b with no parens.
    assert!(rt_expr("no a = b").contains("no a = b"));
}

#[test]
fn card_absorbs_looser_and_prints_bare() {
    // # is looser than ++, so #(a ++ b) prints as #a ++ b... check bare form.
    assert!(rt_expr("#a + b").contains("#a + b"));
    assert!(rt_expr("a ++ (#b)").contains("a ++ (#b)"));
}

#[test]
fn dot_and_prime_binding() {
    assert!(rt_expr("a.b.c").contains("a.b.c"));
    assert!(rt_expr("a.b'").contains("a.b'"));
    assert!(rt_expr("(a.b)'").contains("(a.b)'"));
    assert!(rt_expr("~a.b").contains("~a.b"));
    assert!(rt_expr("~(a.b)").contains("~(a.b)"));
}

#[test]
fn seq_tier_parenthesizes_when_nested() {
    assert!(rt_expr("a ; b ; c").contains("a ; b ; c"));
}

// -- Round-trip coverage across every construct family --------------------

#[test]
fn roundtrip_expression_families() {
    let cases = [
        // logical / temporal binaries
        "p || q",
        "p and q",
        "p <=> q",
        "p until q",
        "p releases q releases r",
        "before after eventually always p",
        "historically once p",
        // comparisons, negated forms (all spellings)
        "a = b",
        "a != b",
        "a in b",
        "a !in b",
        "a < b",
        "a !< b",
        "a =< b",
        "a !<= b",
        "a >= b",
        "a !>= b",
        // relational
        "a . b",
        "a ++ b",
        "a & b",
        "a <: b",
        "a :> b",
        "~a",
        "^a",
        "*a",
        "a'",
        "a''",
        // integer / cardinality
        "#a",
        "int a",
        "sum a",
        "a fun/add b",
        "a fun/sub b fun/mul c",
        "a fun/div b fun/rem c",
        "a << b >> c >>> d",
        "-3",
        "a - 3",
        "a - -3",
        // arrows with every multiplicity combination
        "a -> b",
        "a some -> b",
        "a -> one b",
        "a lone -> some b",
        "a set -> set b",
        // constants, names, at-names, this
        "none + univ + iden",
        "this.foo",
        "@x + y",
        "this/foo/bar",
        "seq/Int",
        "pred/totalOrder[a, b]",
        "fun/min + fun/max + fun/next",
        // box join / call, empty args fold
        "f[x, y]",
        "a.b[c].d",
        // quantifiers, binders, comprehensions
        "all x: A | p",
        "all disj x, y: A | x != y",
        "some x: A, y: B | x in y",
        "no x: A | p",
        "sum x: A | int x",
        "let x = a, y = b | x + y",
        "{ x: A | p }",
        "{ x: A, y: B }",
        "{ disj x, y: A | x != y }",
        // strings and escapes
        r#"s = "hello""#,
        // A raw (literal) tab inside a string is legal and must pass through.
        "s = \"tab\ttab\"",
        r#"s = "line\nbreak\"q\\z""#,
        // if-then-else
        "p => q else r",
        "p => q else r => s else t",
        // blocks and sequencing
        "{ p q r }",
        "a ; b",
    ];
    for case in cases {
        rt_expr(case);
    }
}

#[test]
fn roundtrip_paragraph_families() {
    let cases: &[&str] = &[
        // module header + opens
        "module top",
        "module util/ordering[exactly A, B]",
        "open util/ordering[Node] as ord",
        "private open util/integer",
        // sigs: quals, multi-name, parents, fields with markers, appended fact
        "sig A {}",
        "abstract sig A, B extends P {}",
        "var one sig S in P + Q {}",
        "private lone sig S = P + Q {}",
        "sig A { f: A, g: set A, h: lone A -> one B }",
        "sig A { var disj f, g: A } { f in g }",
        "sig A { x = A }",
        // enums
        "enum Color { Red, Green, Blue }",
        // facts / asserts, ident and string names
        "fact { some A }",
        "fact named { some A }",
        r#"fact "a string name" { some A }"#,
        "assert { no A }",
        r#"assert "s" { no A }"#,
        // preds / funs: receivers, params (both bracket kinds), private
        "pred p { some A }",
        "pred p[x: A, y: B] { x != y }",
        "pred A.p[x: B] { x in this }",
        "private pred p(x: A) { some x }",
        "fun f: A { A }",
        "fun f[x: A]: set B { x.r }",
        "fun A.g[x: B]: one C { c }",
        // macros
        "let m = a + b",
        "let m[x, y] = x -> y",
        "let m { some A }",
        "private let m = univ",
        // commands: labels, name/block targets, scopes, expect, followups
        "run p",
        "run { some A }",
        "c: run p",
        "check a for 3",
        "run p for 3 but exactly 2 A, 4 int, 1..5 steps",
        "run p for 5 String, 2..4 Node",
        "run p for 3 Node, 2 seq expect 1",
        "check a for 3 expect 0",
        "run p expect 2",
        "run p => check a => run q",
    ];
    for case in cases {
        rt(case);
    }
}

// -- Snapshots: pin the exact rendering of a whole module -----------------

#[test]
fn snapshot_whole_module() {
    let src = r"
        module util/ordering[exactly Elem]
        open util/integer as ui
        abstract sig Node { var edges: set Node, val: one Int }
        one sig Root extends Node {} { no edges }
        enum Color { R, G, B }
        fact wellformed { all n: Node | n !in n.^edges }
        pred reachable[a, b: Node] { b in a.*edges }
        fun degree[n: Node]: Int { #n.edges }
        assert acyclic { no n: Node | n in n.^edges }
        check acyclic for 5 but exactly 1 Root expect 0
        run reachable for 4 Node
    ";
    let ast = parse(src, file()).expect("parse");
    let printed = pretty_to_string(&ast);
    // The printed form must itself round-trip.
    rt(&printed);
    insta::assert_snapshot!(printed);
}

#[test]
fn snapshot_precedence_and_temporal() {
    let src = r"
        pred p {
          a + b & c = d
          all x: A | x.field' in x.field
          always (eventually done)
          (a => b) => c
          x = -1
          f[a, b] . g
          no disj a, b: S | a & b != none
        }
    ";
    let ast = parse(src, file()).expect("parse");
    let printed = pretty_to_string(&ast);
    rt(&printed);
    insta::assert_snapshot!(printed);
}

#[test]
fn snapshot_dump_shape() {
    let src = "sig A { f: set A -> one B } fact { a !in b.^c }";
    let ast = parse(src, file()).expect("parse");
    insta::assert_snapshot!(dump(&ast));
}
