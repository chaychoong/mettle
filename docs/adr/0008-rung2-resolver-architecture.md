# ADR-0008 — Rung-2 resolver & type-checker architecture (`als-types`)

**Status:** Accepted (tech-lead review 2026-07-16: contract spot-verified against
sources + 6 independent jar re-probes, zero divergences) · **Date:** 2026-07-16 ·
**Beads:** mt-016 (this contract), mt-017/mt-015/mt-018/mt-019/mt-020

## Context

Rung 2 turns a parsed `Ast` ([ADR-0005](0005-core-ir-type-skeleton.md), Rung 1)
into a **resolved, type-checked world**: names bound, sig hierarchy built, fields
and funcs/preds/facts/asserts/commands type-checked, and the exact accept/reject
verdict of the reference's `CompModule.resolveAll` reproduced. The behavior is
pinned in [reference/alloy6-resolution.md](../reference/alloy6-resolution.md)
(mt-016) against the jar at commit `794226dd`; this ADR proposes the *Rust
structure* that pins it — **semantics faithful, structure idiomatic** (PORTING
prime directive). The rung gate (mt-020) is: **same ACCEPT/REJECT decision as the
jar** on `resolveAll`, 100% on the 167-file corpus and triaged agreement on the
150,891 alloy4fun codes.

The reference's resolver is a 2,700-line mutable `CompModule` with a `HashMap`-
heavy symbol table, object-identity sigs, a bottom-up `VisitReturn<Expr>`
type-checker, and a top-down `resolve(relevantType)` pass that mutates ambiguous
`ExprChoice` nodes into resolved ones. We reproduce its *observable* two-pass
algorithm without porting any of that shape (STYLE M1, PORTING legal hygiene).

## Decision

1. **Home crate `als-types`, one phase, new arenas.** `als-types` takes the Rung-1
   `Ast` (borrowed) and the module graph and produces a new **`ResolvedWorld`**
   value: arena-owned resolved sigs, fields, funcs, and type-checked IR-facing
   expressions, plus the diagnostics. It does not mutate the `Ast` (unlike the
   reference's in-place rewrite) — a phase takes input arenas and produces new
   ones (STYLE A2). No solving, no bounds, no CNF (that is `als-core`, later
   rungs).

2. **Typed-ID symbol tables, no object identity, no `Rc<RefCell>`.** Sigs, fields,
   funcs, params, and let/quantifier binders are arena entries with `SigId`,
   `FieldId`, `FuncId`, `VarId` newtypes (`define_id!`, reusing the ADR-0005
   `Arena<I,T>`). The reference's `new2old`/`sig2module`/object-identity maps
   become ordinary index links (PORTING R3/R5): a `SigId` *is* the resolved sig;
   its module, parent(s), and fields are `SigId`/`ModuleId`/`FieldId` fields.
   Name→id lookup tables are **`IndexMap`** (insertion order = declaration order,
   STYLE D2/C2) so resolution order — and thus the single surfaced error — is
   deterministic without copying the JVM's `HashMap` order (resolution §8).

3. **Module graph is a small owned DAG (`ModuleId` arena).** mt-017 builds it:
   file search order and the jar-stdlib fallback (resolution §2.1), parametric
   instantiation with **instance identity = (filename, resolved-params)**
   (§2.3), `as`/auto-alias tables and qualified lookup (§2.4), private-visibility
   filtering (§2.5), and cycle detection by filename-on-path. Opens/params are
   `ModuleId`/`SigId` edges, not pointers. The embedded stdlib (mt-015) is loaded
   as the last resolver of an `open` target.

4. **The two passes are two explicit functions over a threaded `Ctx`, not a
   visitor.** Mirroring the reference's `Context` behaviorally (PORTING R1: closed
   `Expr` enum + exhaustive `match`, no `VisitReturn`):
   - **Pass A — bottom-up bounding types.** `infer(ctx, expr) -> Typed` walks the
     surface `Expr`, computes each node's `Type` from its children, collects
     candidate sets at ambiguous leaves/joins into a `Choice { candidates,
     reasons, weights }` node, and records `ErrorType`s. Name lookup follows the
     exact scope chain in resolution §4.4 (qualified prefix → local env → macros →
     globals → builtins → sigs/params → funcs/preds → fields, with the
     implicit-`this` first-arg and field-join candidates inside a sig context,
     mode-1 only).
   - **Pass B — top-down disambiguation.** `resolve(ctx, typed, relevant_type)`
     pushes the relevant type down, resolves each `Choice` by the
     `ExprChoice.resolveHelper` algorithm (exact-intersect → common-arity →
     min-weight → resolve-and-retry-once → all-empty⇒`none` → ambiguity/no-match
     error, §4.4), and emits relevance/redundancy **warnings**. `resolve_as_{set,
     formula,int}` are the three typecheck→resolve→typecheck wrappers (§4.3), with
     **no `int`↔`Int` coercion** (§4.5 — the historical casts stay dead).

5. **`Type` is a value type: union of products of `SigId`.** A `Type` is `{ is_bool:
   bool, entries: Vec<Product> }` with `Product(SmallVec<SigId>)` and a cached
   arity bitmask; `is_int`/`is_small_int` are computed/flagged as in the reference
   (§4.1). Subsumption on `add` keeps maximal products per arity. `EMPTY` (no
   entries, not bool) is the ill-typed sentinel; the invariant **`type == EMPTY
   iff errors nonempty`** is a `debug_assert!` (STYLE I1). Builtins `univ/Int/
   seq/Int/String/none/iden` are fixed `SigId`s seeded into every world.

6. **Diagnostics are typed, spanned, render-free (STYLE E1/E3/G3).** Two enums in
   `als-types`: `ResolveError` (the §5.1 reject set — each variant carries the
   `Span`(s) and the ids/names involved, e.g. `CyclicInheritance(SigId, Span)`,
   `AmbiguousName { span, candidates: Vec<Reason> }`, `ArityMismatch { op, span,
   left: Type, right: Type }`) and `ResolveWarning` (the §5.2 catalog). **Errors
   are values, never printed here** — mt-019's `mettle check` renders them through
   the mt-013 caret renderer, exactly like `ParseError`. The resolver returns
   `Result<ResolvedWorld, ResolveError>` for the reject boundary **plus** a
   `Vec<ResolveWarning>` on success; **warnings never turn a success into a
   failure** (§0, §5.3) — that is the mt-020 gauge contract.

7. **First-error semantics, deterministic.** The reference throws the *first*
   `JoinableList` error (`errors.pick()`). mettle collects errors during a phase
   but surfaces the **first by source position** as the `Err` (deterministic and
   caret-friendly), matching the reference's accept/reject decision (which error
   is *shown* is not gauged; *that* it rejects is). Warning order is fixed by
   `Span` (the reference's `HashMap`-iterated implicit-conjunction order is
   incidental — resolution §8).

8. **Reject/warn parity is the only gauge; keep the taxonomy exhaustive.** Every
   §5.1 row is a `ResolveError` variant; every §5.2 stem a `ResolveWarning`
   variant. No `_` catch-all (PORTING R1) so a missed case is a compile error, not
   a silent wrong verdict. Each mt-020 disagreement becomes a committed regression
   test citing its resolution-doc §/probe id (STYLE U3).

### Explicitly out of Rung 2 (no solving)
Bounds, universe/atom numbering, CNF, symmetry, `util/ordering`'s exact-bounds
special-casing at the *solver* level, overflow, and instance decoding all stay in
`als-core`/`als-solve`/later rungs. Rung 2 stops at "resolved + type-checked +
accept/reject/warn verdict". Well-typed temporal models **resolve** (they are
ACCEPT); "parsed/resolved, not yet solvable" is a downstream typed error (STYLE
T2), not a Rung-2 reject.

## Consequences
- mt-017 (module graph) and mt-015 (clean-room stdlib) land together — each needs
  the other to be exercisable — then mt-018 (resolver core) fills passes A/B, then
  mt-019 (`mettle check`) renders diagnostics, then mt-020 gauges. This matches
  the STATE.md sequencing.
- `als-types` gains typed diagnostics as its public surface; `als-syntax`
  (`ParseError`) and `als-types` (`ResolveError`) are separate enums per phase
  (STYLE E1). `mettle check` is the join point (E3).
- Meta-sig (`$`) synthesis, recursion (allowed — no resolve-time check), and macro
  depth-limit-20 are behaviors mt-018 must carry; `util/integer` name-based
  special-casing (§7) is a small explicit branch, Ledger-tracked.
- The stdlib special-casing that is *analyzer* behavior rather than `.als` text
  (`util/ordering` exact bounds + symmetry) is deferred to its own
  SEMANTICS_LEDGER entries at solve time — noted in mt-015/mt-017, not built here.

## Alternatives considered
- **Port `CompModule` shape** (one mutable world, `VisitReturn`, in-place `Expr`
  rewrite, object-identity sigs). Rejected: violates PORTING R1/R3/R7 and STYLE
  §6; object identity + `HashMap` order is exactly the non-determinism we must not
  inherit (D2).
- **Fuse the two passes into one bidirectional walk.** Rejected: the reference's
  correctness — especially overload disambiguation and relevance warnings —
  depends on a *completed* bottom-up type before the top-down relevant type is
  known (`ExprChoice.resolve` needs every candidate's finished type). Two passes
  keep the contract legible and testable.
- **Resolve in `als-syntax`** (extend the parser). Rejected: name/type resolution
  is a distinct phase over the module graph (STYLE S3); `als-types` is its home
  crate by the workspace DAG.
- **Model resolution mode 2** (universal implicit `this`). Rejected: unreachable
  from the jar's public API (§0); implementing it would be untested dead code and
  a conformance liability.

Related: [ADR-0005](0005-core-ir-type-skeleton.md) (arenas/AST/IR shapes),
[ADR-0007](0007-rung1-lexer-parser-architecture.md) (the authority-chain
precedent), [ADR-0006](0006-licensing-posture.md) (clean-room stdlib),
[reference/alloy6-resolution.md](../reference/alloy6-resolution.md) (the pinned
behavior this structure implements).
