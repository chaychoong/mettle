# ADR-0007 — Rung-1 syntax front end: hand-written lexer + recursive-descent/Pratt parser

**Status:** accepted (2026-07-15) · **Beads:** mt-010, mt-011 · **Owner:** tech lead

## Decision

1. **Hand-written lexer** in `als-syntax` producing a `Vec<Token>` (kind + `Span`),
   implementing [reference/alloy6-grammar.md §1](../reference/alloy6-grammar.md)
   exactly. Token-stream rewrites F1–F4 (§2) are implemented as a separate,
   unit-testable *cooking* pass over the raw token stream (mirroring the
   observable behavior of the reference's filter, not its structure).
2. **Hand-written recursive-descent parser** with a precedence-climbing (Pratt)
   expression core over the pinned 21-level table (§3), producing the arena
   `Ast` of ADR-0005. No parser generator, no combinator library.
3. **Error strategy for Rung 1: fail fast, precisely.** The parser stops at the
   first syntax error with a typed `ParseError` carrying span + expected-set
   (STYLE E1/G3). Error *recovery* (multi-error reporting) is deliberately
   deferred to mt-013, where diagnostics quality gets its own pass against the
   Alloy4Fun corpus.
4. **Authority chain** for any syntax question: `alloy6-grammar.md` → the jar
   (empirical test, then update the doc) → never memory or the public grammar
   appendix (it is out of date vs. the implementation).

## Why hand-written (vs. LALR/PEG generators, chumsky/logos, tree-sitter)

- The reference language is *not* cleanly context-free at the token level: it
  needs a token filter (label reordering, `not`-comparison merging, arrow
  merging, minus-folding, quantifier-vs-multiplicity lookahead). Hand-written
  code expresses these directly; grammar generators fight them.
- Deterministic, dependency-free (STYLE P1/P2: zero new deps for the front
  end), fully spanned, and the error messages stay ours to shape (diagnostics
  are a headline feature, G3).
- rustc, rust-analyzer and most production compilers use exactly this shape;
  it is the idiomatic Rust answer (PORTING_RULES prime directive: behavior
  faithful, structure idiomatic).

## Shape constraints (binding for mt-010/mt-011)

- Lexer: `struct Lexer<'src>` over `&str` + `FileId`; emits `Token { kind: TokenKind, span: Span }`;
  errors are values (`TokenKind::Error` is NOT used — lexing returns
  `Result<Vec<Token>, LexError>`; first error wins for Rung 1).
- Keywords resolved by exact match after identifier scan (single keyword table,
  sorted, `binary_search` or `match` — no hashing in a numbering path; D2 does
  not bite here but keep it boring).
- Parser: `struct Parser` consuming the cooked token slice; builds `Ast`
  arenas; every node span-covered; `#[cfg(test)]` unit tests colocated;
  snapshot tests (insta) arrive with the mt-012 pretty-printer.
- The corpus gauge for Rung 1: % of `corpus/alloytools-models` + `corpus/portus-63`
  files that lex (mt-010) and parse (mt-011) without error. Target: 100% on
  both corpora; every failure is triaged (our bug vs. genuinely invalid file)
  before Rung 1 closes.

## Consequences

- One new dev-dependency planned at mt-012: `insta` (snapshot testing, U2).
  No runtime dependencies added by Rung 1.
- The AST gains grammar-parity extensions (same commit as this ADR):
  `SigParent::Eq`, macros as paragraphs, string paragraph names, right-side
  `disj` in decls, integer-function operators, `int e`/`sum e` casts,
  `ExactlyOf` defined-decl marker, generalized scope bounds (ranges/increments,
  `steps`/`String` targets), command follow-up chaining.
- Supersedes nothing. Related: ADR-0005 (AST shapes), ADR-0002 (oracle).
