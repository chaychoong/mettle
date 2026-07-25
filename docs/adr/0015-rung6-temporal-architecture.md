# ADR-0015 — Rung-6 temporal architecture: bounded lasso solving on the existing engine

**Status:** Proposed · **Date:** 2026-07-26 · **Beads:** mt-063/mt-064 (the
pinned contract, [reference/alloy6-temporal.md](../reference/alloy6-temporal.md)),
mt-065–mt-069 (implementation, cut below)

## Context

Rung 6 makes mettle "do time": temporal Alloy 6 (`var`, the 11 temporal
operators, `steps` scopes) for bounded checks, closing the 22
`lower:temporal` corpus defers. The contract is pinned across two probe
waves; the facts that force the architecture:

- A command is **temporal** iff its model reaches any `var` sig/field or any
  temporal operator (string-pinned discriminator, `CompUtil.java:189-201`).
- `steps` is a **range** `[min,max]` (bare `for N` = `[1,N]`, default
  `[1,10]`, `exactly N` = `N..N`); the jar solves **incrementally per
  length k**, returning the first (minimal) SAT. UNSAT means "no
  counterexample within the bound" — nothing stronger.
- Every SAT temporal instance is a **lasso**: k states plus a back-loop
  state `l ∈ [0,k-1]`. Finite non-looping traces do not exist in this
  engine.
- **Skolemization is disabled under any temporal operator**
  (`Skolemizer.java:494-526`) and **symmetry breaking runs per-state with
  skolems excluded** (`SymmetryBreaker.java:213-232`) — both simplify
  mettle's port; the hard parts of Rung-4 skolemization stay out of the
  temporal path by the jar's own design.
- The only open scope form, `1..` (unbounded), is **rejected** by the
  jar's default bounded engine (`ErrorAPI("Bounded engines do not support
  complete model checking.")`); unbounded solving requires the external
  `electrod.elo` binary.
- Rendering: one instance per state; the XML encodes the loop as
  `looplength = tracelength − loopState`; `A4Solution.toString(state)` is
  pinned byte-level. Post-solve eval takes a state index that **wraps
  through the loop** for `state ≥ traceLength` and clamps negatives to 0;
  all 11 temporal operators are legal evaluator input, evaluated relative
  to the given state.
- Enumeration (`next()`/`fork(p)`) exhausts each trace length before
  advancing to the next; `fork(p)` holds states `0..p−1` fixed. Wave 2
  classified the GUI's four operators onto these primitives.

## Decision

**Bounded lasso solving as k-fold unrolling over the existing,
unmodified CDCL engine — one deterministic encode+solve per trace length,
in ascending order, first SAT wins.** No new solver, no incrementality
across lengths (correct first; the mt-057/mt-059 lesson says measure
before optimizing, and per-length encodes keep determinism trivial).

1. **IR & bounds (mt-065):** the relation table gains a static/variable
   partition keyed off `var`. For a trace length k, each variable relation
   is instantiated k times (per-state copies through the existing
   `Bounds`/universe machinery — atoms are rigid, only relation values
   vary); static relations bind once. The lasso is a selector: one
   loop-index variable set `l ∈ [0,k-1]`, exactly-one-encoded.
2. **Lowering (mt-066):** temporal formulas lower by the standard
   LTL-on-lasso translation — a formula is lowered *at a state index*,
   `'`/`after` step through the successor function (which follows the
   back-loop at state k−1), past operators walk the honest prefix, and
   `always`/`eventually`/`until`/`releases` expand over the k states with
   loop closure. Skolemization under temporal operators is blocked with
   the existing `Pol.blocked` machinery (the jar-conform rule is already
   pinned and partially shipped at mt-055).
3. **Solve driver & verdicts (mt-067):** `for k in [min,max]` — encode,
   solve, return the first SAT as a k-state lasso trace; exhausting the
   range yields UNSAT-within-bound. Typed defers: `1..` (unbounded) gets
   the jar's exact rejection text; `check … for 1 steps` awaits the
   ledgered owner fork (the jar NPEs there — mettle cannot conform to a
   crash) and until decided is a typed defer naming the bug. Symmetry
   breaking applies per-state per the pinned rule.
4. **Surface (mt-068):** `exec` renders traces state-by-state against the
   pinned `toString(state)` shapes with the loop marked; the REPL gains a
   state index with the pinned wrap/clamp semantics, making it the trace
   debugger ADR-0014 promised. Enumeration operators are *classified*
   (typed, honest) but mettle-side trace enumeration semantics are a
   later, separate decision.
5. **Conformance arm (mt-069):** bank fresh jar verdicts for the 4
   temporal files (22 commands — observed in wave 1, not yet baselined),
   grow the gauge's temporal bucket into real comparisons, and port the
   load-bearing probe cells into jar-free conformance tests. The counting
   nets take temporal commands only where the SB-0 baseline holds a real
   count (leader.als's entry was reproduced live in wave 2).

**Out of scope, disclosed:** unbounded model checking (electrod). mettle
matches the jar-without-electrod, which is the jar's own out-of-the-box
behavior; the pinned rejection text is the conformance surface. Recorded
in LIMITATIONS when the driver ships.

## Consequences

- The determinism contract extends unchanged: per-length encodes are
  deterministic, so verdicts, traces, and the sweep hash stay
  byte-reproducible at any job count.
- Encoding cost multiplies by trace length (k copies of every variable
  relation). The gauge's budget taxonomy (capacity/over_budget) already
  prices this honestly; no new budget machinery is needed up front.
- The `check`-at-length-1 owner decision (Ledger tracked corner) gates
  only that boundary case, not the rung — implementation proceeds with a
  typed defer there.
- Enumeration/counting semantics for traces are deliberately deferred
  behind verdict conformance — the scorecard's temporal arm is verdicts
  first, counts only where a baseline exists.

## Alternatives considered

- **Port Pardinus's incremental translation** (reuse clauses across
  lengths): faster in principle, but it couples the encoder to solver
  internals, threatens the determinism contract, and optimizes before the
  bottleneck is measured — rejected for the first cut by ADR-0013's
  logic.
- **A native temporal solver layer (BMC in the solver):** rejected —
  mettle's CDCL is deliberately dependency-free and verdict-focused; the
  unrolling belongs in the translation layer where the jar itself does it.
- **Implementing unbounded solving (electrod parity):** rejected for the
  rung — it is optional in the jar itself and out of the drop-in
  baseline.
