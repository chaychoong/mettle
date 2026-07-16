# ADR-0011 — Rung-3 translation & solving architecture (`als-core` + `als-solve`)

**Status:** Accepted (solver decision — write our own CDCL — made by the product
owner 2026-07-16; architecture reviewed and accepted by the tech lead) ·
**Date:** 2026-07-16 · **Beads:** mt-028 (this contract), mt-029+
(implementation, to be filed)

## Context

Rung 3 turns a resolved, type-checked world ([ADR-0008](0008-rung2-resolver-architecture.md),
Rung 2) into a **verdict**: `mettle run`/`check` returns a correct instance or
"no counterexample", self-verified (ROADMAP rung 3). The reference behavior is
pinned in [reference/alloy6-translation.md](../reference/alloy6-translation.md)
(mt-028) against the jar at commit `794226dd`: scopes → universe → bounds
(`ScopeComputer`/`BoundsComputer`), resolved `Expr` → Kodkod relational AST
(`TranslateAlloyToKodkod`), the SAT boundary and outcome/enumeration semantics
(`A4Solution` over the Pardinus/Kodkod engine and SAT4J).

This ADR proposes the **Rust structure** that pins that behavior — *semantics
faithful, structure idiomatic* (PORTING prime directive) — and makes the rung's
one owner-visible decision: **how mettle gets a SAT solver**. The shapes are
already laid down by [ADR-0005](0005-core-ir-type-skeleton.md): `als-core` has the
three-sorted IR + `Universe`/`TupleSet`/`Bounds`; `als-solve` has the
dependency-free `Var`/`Lit`/`Cnf`/`Assignment`/`Outcome` + the `Solver` trait.
Rung 3 fills flesh behind these bones; it does not redesign them.

The rung gate (ADR-0002): **same verdict (SAT/UNSAT) as the jar**, plus **SB-0
model-count parity** on the counting net. Instances are never diffed against the
jar; instance *validity* is mettle's own evaluator's job (self-check net).

## Decision

### 1. The pipeline is four phases over the ADR-0005 shapes, no Java structure ported.

`als-core` gains a `lower` (translate) module and `als-solve` gains a concrete
solver. The phases (translation-reference §0), each a function taking input arenas
and producing new ones (STYLE A2):

1. **Scope → universe** (`scope.rs`): resolved sigs + a `Command` → a `Universe`
   (the ordered atom list, translation-ref §1.1–1.3) + a per-sig scope table.
   Faithful port of `ScopeComputer`'s fixpoint (abstract-sum → overall → parent),
   the exact/`one`/`lone` rules, bitwidth/maxseq/maxstring, and the
   `Name$index`/ints-ascending/strings atom order.
2. **Bounds** (`bounds.rs` builder): scopes + universe → `als_core::Bounds` (one
   `RelBound` per `RelId`) + the sig-hierarchy/multiplicity/size constraint
   formulas. Faithful port of `BoundsComputer` (leaf/remainder/abstract relation
   allocation, subset sigs, field product bounds, `util/ordering` exact bounds).
3. **Lower to IR** (`lower.rs`): resolved `Expr` → `als_core::ir::{Formula,
   RelExpr, IntExpr}` per the translation-ref §2 mapping table; assemble the goal
   = facts ∧ (command formula | negated assertion) (§2.5).
4. **Translate to CNF + solve** (`cnf.rs` + `als-solve`): bounded IR + bounds →
   `als_solve::Cnf` (a relation's tuples become boolean variables in the fixed
   atom×relation order, relational ops become clauses — the classic
   bounds-relational-to-SAT encoding), solve, decode `Assignment` → instance.

No `CompModule`/`A4Solution` mega-object, no `IdentityHashMap`, no visitor: closed
enums + exhaustive `match` over the existing IR (PORTING R1), typed-ID arenas
(R3), determinism by construction (D2).

### 2. The solver: **hand-rolled CDCL in `als-solve`, zero dependencies.** (the rung's biggest decision)

`als-solve` implements a small, deterministic **CDCL SAT solver** behind the
existing `Solver` trait — no vendored/bound external solver for the default path.
Rationale, weighed against the two alternatives:

- **Determinism & byte-identical output (STYLE D1, ADR-0002 item 4)** is the
  decisive factor. mettle's north-star gauge and its whole test story depend on a
  *fixed solver build giving byte-identical output and enumeration order*. A
  hand-rolled solver with fixed decision heuristics and fixed variable order gives
  this by construction. A vendored solver (even a Rust one) makes determinism a
  property we must audit and pin across versions; an FFI/native solver (MiniSat,
  Glucose, CaDiCaL) adds build-time native deps, platform variance, and
  enumeration-order we don't control — directly against the "single static binary,
  no native deps" north star.
- **Licensing (ADR-0006).** mettle ships **MPL-2.0**, clean. A hand-rolled solver
  is our own MPL-2.0 code. Vendoring pulls in another license to track
  (SAT4J = LGPL; MiniSat = MIT; Glucose = MIT-ish; CaDiCaL = MIT) — MIT-family is
  compatible but each is one more obligation, and an LGPL/native path is a
  redistribution question we don't want in the shipped artifact.
- **Zero-dep boundary already designed for this.** ADR-0005 item 6 deliberately
  made `als-solve` dependency-free with `Solver` as *the* open extension point
  (PORTING R2b): "pure-Rust SAT first, FFI later behind the same boundary." This
  ADR executes that plan — it does not introduce it.
- **Cost is bounded and one-time.** A correct CDCL core (unit propagation with
  watched literals, 1-UIP conflict analysis, VSIDS or a simpler fixed heuristic,
  restarts) is a well-understood ~1–2k-line component. Rung 3's models are small
  (scope 3–5); raw performance is not the gauge, verdict correctness + determinism
  are. Performance work (better heuristics, or an *optional* FFI backend behind
  the same trait for large models) is a later, non-gating optimization.

**Recommendation: build the CDCL solver in `als-solve`.** Keep the `Solver` trait
as the seam so an *optional* high-performance FFI backend can be added later
(feature-gated, never the default, never in the conformance path) without
touching the translator. The incremental/assumption interface the trait needs for
**enumeration** (block each found model with a fresh clause — translation-ref §4.5)
is added now, as ADR-0005 item 6 anticipated.

*Alternatives considered and rejected for the default path:* (a) **vendor a
pure-Rust solver** (e.g. varisat/splr) — pulls a dependency + its license, and
makes determinism/enumeration-order a property we audit rather than own; (b)
**FFI to MiniSat/CaDiCaL** — native build deps + platform variance, against the
static-binary north star; both remain viable *optional* backends behind the trait
if a later rung needs raw speed.

### 3. Determinism strategy (atom numbering + CNF variable allocation).

- **Atom order** is fixed once, in phase 1, by translation-ref §1.3 (sigs in
  declaration order → atoms `Name$0…` in index order → integer atoms ascending →
  string atoms). This is the single canonical order; `als_core::Universe` already
  stores it as an ordered `Vec`.
- **CNF variables** are minted densely, in a fixed nested order: for each relation
  in `RelId` order, for each candidate tuple in `TupleSet` lexicographic order
  (both already BTree/append-ordered in the skeleton), mint one `Var`. `als_solve::
  Cnf` already asserts dense insertion-order numbering.
- **The CDCL solver's own choices** (decision order, restart schedule) are fixed
  by the build; no wall-clock, no hash-map iteration, no RNG-without-fixed-seed
  near numbering/output (STYLE D2). Enumeration blocks models with a fresh clause
  in a fixed order, giving a stable enumeration sequence.
- mettle matches the jar on **verdict** and **SB-0 count**, never on CNF shape or
  instance tuples (ADR-0002).

### 4. Symmetry breaking: **none in Rung 3.** (translation-ref §3)

The counting net runs at `symmetry = 0` (raw satisfying assignments) — the only
regime where a count is solver-independent and comparable — and mettle's core has
no symmetry breaking, so it *is* that regime. Rung 3 ships zero lex-leader
machinery and is gauged on verdict + SB-0 count. Default-symmetry (SB=20) count
parity needs bit-exact lex-leader replication and is a later dedicated net
(explicitly out of scope per ADR-0002). **But** the `expect 1 ⇒ symmetry 0`
coupling (translation-ref §3, probe T3) must be honored so the harness compares
like-for-like — the mt-006 oracle harness already sets symmetry explicitly.

### 5. Self-verification is the gate's teeth. (translation-ref §6)

After finding an instance, mettle **evaluates the full goal formula against that
instance with its own evaluator and asserts it is `true`** (a `debug_assert!`;
ADR-0002 item 2). A found instance that fails its own formula is a mettle bug,
never a user error. This delivers the ROADMAP's "self-verified" promise without
ever diffing the jar's tuples, and it is the substrate for the later REPL (Rung 5)
and `check`-counterexample explanation.

### What the Rung-3 vertical slice includes vs. defers.

**Includes** (enough real models to satisfy the rung gate on the corpus): sigs
(prim/abstract/subset/`one`/`lone`/`some`), fields + field multiplicities, facts +
sig facts, `run`/`check` with scopes (default + `for N but …` + `exactly`),
relational operators, quantifiers (direct, skolemization optional), multiplicity
tests, comprehensions, `let`, `util/ordering` (exact bounds), and enough integer
support to not reject int-using models (cardinality `#`, `int`/`Int` casts) — with
the **overflow switch** wired (LEDGER-001 default forbid).

**Defers:** full **integer/counting fidelity** (division/remainder corners, `sum`
overflow, `seq/Int` bounds, default-symmetry count parity) → **Rung 4**; **String**
beyond membership → Rung 4; **temporal solving** (`var`, `always`/`until`, trace
scopes, the Pardinus LTL→FOL expansion) → **Rung 6**; **symmetry breaking**,
**unsat cores**, **the `Simplifier` partial-instance pass** (a performance pass
that cannot change a verdict), and an **optional FFI solver backend** → later,
non-gating. Well-typed temporal models still resolve (Rung 2 ACCEPT); "resolved,
not yet solvable" is a typed downstream error (STYLE T2), not a Rung-3 reject.

## Consequences

- Implementation beads (mt-029+) land in dependency order: scope→universe, then
  bounds, then IR lowering + goal assembly, then the CDCL solver + CNF encoding,
  then instance decode + evaluator self-check, then `mettle run`/`check` CLI, then
  the differential solve gauge (the Rung-3 equivalent of mt-020). The proposed
  breakdown is in the mt-028 report; the tech lead files the beads.
- `als-solve` grows from a trait skeleton into a real CDCL solver + incremental
  enumeration, still dependency-free and still behind the `Solver` seam.
- The `util/ordering` exact-bounds behavior needs an **approved** SEMANTICS_LEDGER
  entry before the ordering code ships (draft in translation-ref §5); likewise the
  integer/overflow corners re-confirm LEDGER-001 at solve time.
- The counting net (ADR-0002 Net 3) becomes usable from the first solving bead:
  SB-0 counts are canonical and match the no-SB core.

## Alternatives considered

- **Vendor or FFI a SAT solver for the default path** — rejected for the default
  (determinism, licensing, native-dep/static-binary tension per decision 2);
  retained as an *optional*, non-gating, feature-gated backend behind the `Solver`
  trait for future performance needs.
- **Port `A4Solution` as one mega-object** (mutable solve state, `IdentityHashMap`
  atom maps, Kodkod-shaped bounds) — rejected: violates PORTING R1/R3 and STYLE §6;
  the identity-map iteration order is exactly the non-determinism we must not
  inherit (D2). We reproduce observable behavior, not structure.
- **Implement symmetry breaking now for default-symmetry count parity** — rejected:
  needs bit-exact lex-leader replication, is not the rung gate, and the SB-0 net is
  already canonical (ADR-0002). Deferred to a dedicated later net.
- **Skip the evaluator / trust the solver** — rejected: the self-check net is how
  Rung 3 earns "self-verified" without diffing jar tuples; it is cheap and catches
  translator bugs a verdict-only gauge would miss.

Related: [ADR-0002](0002-conformance-oracle.md) (verdict + SB-0 count gauge,
determinism scope), [ADR-0005](0005-core-ir-type-skeleton.md) (the IR/bounds/CNF
shapes this fills, and the `Solver`-trait extension point), [ADR-0006](0006-licensing-posture.md)
(MPL-2.0, clean-room), [ADR-0008](0008-rung2-resolver-architecture.md) (the Rung-2
resolved world this consumes), [reference/alloy6-translation.md](../reference/alloy6-translation.md)
(the pinned behavior this structure implements), SEMANTICS_LEDGER LEDGER-001
(overflow) + the draft `util/ordering` entry (translation-ref §5).
