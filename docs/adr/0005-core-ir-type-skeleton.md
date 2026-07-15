# ADR-0005 — Core IR type skeleton (arenas, AST, relational IR, CNF boundary)

**Status:** Accepted
**Date:** 2026-07-15
**Bead:** mt-005

## Context
Everything downstream (parser, resolver, translator, solver) hangs off the
core data types. These are the load-bearing, taste-heavy decisions, so they
were hand-designed by the tech lead (per the mt-005 bead), bones only —
later beads fill in flesh behind these shapes.

## Decisions

1. **`als-syntax` is the shared dependency root.** The typed-ID/arena
   infrastructure (`Arena<I, T>`, `ArenaId`, `define_id!`) and `Span`/`FileId`
   live there and are reused by every downstream IR (STYLE S3 wants shared
   helpers in one crate; the workspace DAG already makes `als-syntax` the
   root). `als-solve` deliberately does **not** depend on it — see (6).

2. **One generic `Arena<I, T>` + `u32` newtype IDs** (STYLE §6, PORTING R3).
   The ID type parameter statically pairs each ID with its arena (STYLE A4);
   `define_id!` mints the newtypes. IDs are `u32` (dense, half the size of
   `usize` on 64-bit; arenas >4Gi nodes are an asserted internal error).
   Arenas are append-only; iteration is allocation order — deterministic by
   construction, no hashing anywhere (STYLE D2).

3. **Unified surface `Expr`, three-sorted IR.** Alloy's grammar does not
   distinguish formulas from relational or integer expressions — that split
   is a type-checking result. So the AST (`als-syntax::ast`) has a single
   `Expr` enum, and the relational IR (`als-core::ir`) splits into `Formula`
   / `RelExpr` / `IntExpr` with separate arenas and IDs, mirroring the
   *behavioral* role of Kodkod's formula/expression/int-expression sorts
   while keeping our own idiomatic shape (PORTING prime directive, R1/R2a:
   closed enums, exhaustive match, no visitor).

4. **AST surface-faithfulness choices.**
   - Arrows are a dedicated `Arrow { lhs, lhs_mult, rhs_mult, rhs }` node
     (not 16 `BinOp` variants); comparisons carry a `negated` flag matching
     the `!in`/`!=` surface forms.
   - Box join `f[x]` is one node kind; whether it's a call or a join is a
     resolution question, not a grammar one.
   - Multiplicity markers in declaration bounds (`one A`, `seq A`) are
     `UnOp` variants distinct from the formula prefixes (`one e` the test);
     the parser disambiguates by position.
   - Temporal syntax (var sigs/fields, primes, full connective set, `steps`
     scopes) is first-class from day one (STYLE T1).
   - Every node carries a required `Span` (STYLE G1); IR nodes keep the span
     of the surface construct they lower from (G2).
   - Names are owned `String`s for now; interning is a mechanical later
     change if profiles demand it.

5. **Bounds are `BTree`-ordered.** `TupleSet` is a `BTreeSet<Tuple>` and
   `Bounds` a `BTreeMap<RelId, RelBound>` — deterministic lexicographic /
   `RelId`-order iteration (STYLE C2, key order), with arity and
   lower⊆upper invariants asserted at construction (I1/I4). Atom order is
   fixed at `Universe` construction and is the canonical order everything
   downstream numbers from.

6. **`als-solve` stays dependency-free.** It is the pure SAT boundary: `Var`,
   `Lit` (minisat-style `var<<1|sign` encoding — one-XOR negation), `Cnf`
   (dense insertion-order variable numbering, asserted), `Assignment`,
   `Outcome`, and the `Solver` **trait** — the one genuinely open extension
   point (PORTING R2b), pure-Rust first, FFI later behind the same boundary
   (STYLE P3). No spans here; mapping solver output back to source is the
   decoder's job in `als-core`/`als-instance`.

7. **Overflow semantics live in the translator, not the types.**
   `IntExprKind` carries no wrap/forbid marker; LEDGER-001's forbid-default
   is a translation-time behavior.

8. **Library crates deny `clippy::unwrap_used`/`expect_used`** at the crate
   root (STYLE L3), added to the three crates touched here; the remaining
   crates get it as they gain code.

## Consequences
- Rung-1 parser beads (mt-010..014) build `Ast` values behind these shapes;
  resolver/translator beads target `Ir`/`Bounds`/`Cnf`.
- `no`/`lone`/`one` quantifiers and multi-binding quantifiers do not exist
  in the IR — lowering desugars them to nested `all`/`some` (documented on
  `FormulaKind::Quant`).
- Adding an AST/IR variant forces every consumer site to update (no `_`
  catch-alls on core enums, PORTING R1).

## Alternatives considered
- `Rc<RefCell<..>>` node graphs — rejected outright (STYLE §6, PORTING R3).
- Split formula/expr enums in the *surface* AST (rustc-style separation) —
  rejected: Alloy's grammar genuinely unifies them; a premature split forces
  the parser to duplicate expression parsing or mis-sort nodes it can't yet
  classify.
- String interning now — deferred: adds a shared interner dependency to the
  bones for an unproven win; the `Ident` shape localizes the later change.
- `usize` IDs — rejected: doubles node size on 64-bit for no benefit at our
  scales.
