# ADR-0018 — Encoder structural sharing: value cache, support-bounded closure, widened grounding memo

**Status:** Accepted (tech-lead decision on the mt-080 measured profile) · **Date:** 2026-07-28 ·
**Beads:** mt-080 (the profile), mt-081 (the implementation)

## Context

The mt-078 census left 42 rows encode-bound even at a 128M gate budget
(family C), concentrated in the TransForm `tso_transistency_perturbed*` pair
and `c11_perturbed.als`. The mt-080 instrumented profile (encoder run to
32M-budget exhaustion, gate attribution by conjunct/op-class/memo behavior)
re-ranked the census's mechanism:

- **The dominant cost is duplication under distinct node ids, not matrix
  density or env churn.** `lower.rs` re-lowers every `pred`/`fun` body at
  every call site, minting fresh `RelExprId`s for identical work. The mt-049
  grounding memo keys on `(node id, env)` and is therefore blind to it by
  construction. Measured: TransForm encodes the same ~6 closure *values* 242
  times (181 arena copies of `*co_pa` alone, 12.4M ops); a structural value
  cache saves ≥71% of ops there and ≥79% on c11 — scale-invariant, which is
  why even c11's *solving* sibling burned 20M of its 32M budget.
- **Closure squaring iterates `log2(|universe|)` rounds** where
  `log2(|operand support|)` suffices — 28% of TransForm's ops.
- **The memo's strict-subset env rule** (a node whose free vars equal the
  active environment is never cached) was reasoned from "every binding yields
  a distinct key"; the profile measured that false — the *same* `(node,
  binding)` pair is revisited thousands of times under one binding (7.1% of
  c11's ops).

## Decision

Three changes in `als-core::encode`, one review invariant each:

1. **Structural value cache.** Every produced matrix is interned by full
   structural content — `(arity, BTree-ordered (tuple, cell key) list)` where
   the cell key is injective over `Bool` (`Const(false)`/`Const(true)`/
   `2 + Lit::code()`) — to a dense `MatrixId`; operation results are cached
   under `(op tag, lhs id, rhs id)`. **No lossy-hash equality anywhere**: a
   cache hit means the operands are structurally identical, so the previously
   minted gates compute the same function — reuse is sound by construction.
   All tables are `BTreeMap`s; ids are minted in first-encounter order
   (deterministic). Caches hold `MatrixId`, matrices live once in a
   side table, and operands are materialised only on a miss — the naive
   variant that stored matrices in the caches was built first and measured
   at 2.96 GB RSS with c11 still over budget; the id-plumbed version lands
   c11 at 0.55M spend / 164 MB. Interning effort is metered into the same
   budget counter, so the gate budget still bounds time. `Transpose` is
   excluded from sharing (mints no gates).
2. **Support-bounded closure.** `closure()` runs `⌈log₂(support)⌉` squaring
   rounds — the operand's atom set read off its BTree keys — instead of
   `⌈log₂(|universe|)⌉`. Sound because a simple path or cycle over the
   support visits each atom at most once, and `2^rounds ≥ support` covers
   both; this is Kodkod's own matrix-dimension bound, so it moves *toward*
   the reference. Verified against a brute-force relaxation oracle,
   exhaustively for every binary relation over 1..=4 atoms plus seeded random
   matrices to n=12.
3. **Widened grounding memo.** `env_key` now admits nodes whose free-var set
   equals the environment; the memo holds an entry per `(node, binding)`
   actually visited. The cost is memory, accepted on the measured numbers.

## Consequences

- Both mt-080 subject rows clear the ceiling with large margins: TransForm
  minality_check[6] 33.6M→6.67M (now SAT in under a second), c11[7]
  33.6M→0.55M. Family-C conversions land in the default-regime scorecard
  (fresh battery figures in the mt-081 bead and STATE).
- One measured side effect, disclosed in full: five rows move
  agree → over_budget at default conflicts (net movement +24/−5 = +19).
  The shared, smaller CNF is harder for the solver on some previously-easy
  rows: `ringlead.als[2]` and `etl_scd.als[5]` recover to agreement at 50k
  conflicts, but `OLAPUsagePrefs.als[0]`, `elevator_spl_events.als[29]`, and
  `life.als[1]` remain over_budget even there — durably lost at every probed
  budget, plausibly because merging duplicate subcircuits removes the
  per-copy auxiliary diversity VSIDS was exploiting on those SAT rows. All
  five are typed defers, never wrong verdicts. Follow-up filed (mt-082): the
  ADR-0017 pairing rule applies to encoder-shape changes too — the conflicts
  default gets a paired re-measurement on the new CNF shape, where the
  cheaper wall (stage-1 588s→478s) buys headroom.
- Auxiliary variable numbering shifts (fewer gates minted). Legal under the
  determinism contract — run-to-run byte-identity holds (tested); CNF-size
  snapshots move.
- The mt-049 memo comment's original rationale is superseded in place with
  the measured refutation.

## Alternatives considered

- **IR hash-consing in `lower.rs` (interning nodes at mint time).** Strictly
  larger payoff — it would collapse the 601k-node c11 arena and make the
  existing memo see through inlining — but interning merges differing spans
  (diagnostics regression risk) and turns the IR tree into a DAG for every
  downstream tree-walker (free-vars, overflow guard, self-check).
  **Deferred, not rejected**: evaluate once the value cache's sweep history
  is established.
- **Ranking/level-variable acyclicity encodings.** Rejected outright: new
  primary variables would change the model set and break the SB-0
  counting-net contract (exact count parity with the jar).
- **Mask-aware closure for `no iden & ^r`** — measured at 1.6% of the
  dominant row's ops; not worth its complexity.
- **Dense matrix representation** — cuts wall-clock constant factors, not
  gate counts; changes no deferral verdict.
