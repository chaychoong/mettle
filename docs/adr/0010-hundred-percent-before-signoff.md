# ADR-0010 — Owner gate: ~100% resolve similarity before the Rung-2 touchpoint

**Status:** Accepted (product owner decision) · **Date:** 2026-07-16 ·
**Beads:** mt-022, mt-023 · **Supersedes:** the *scheduling* posture of
[ADR-0009](0009-fused-resolve-pass-accept-lean.md) ("leave accept-lean until
scorecard pressure warrants"); ADR-0009's technical findings stand.

## Context

Rung 2 closed at mt-020 with 0 jar-accepts/mettle-rejects and 95.82% total
alloy4fun agreement; the 4.2% remainder is over-acceptance whose measured root
cause is coarse bounding types (ADR-0009 outcome). The plan of record was to
schedule the precise-types fix (mt-022) opportunistically. The product owner
instead set a product gate: **testing starts at ~100% similarity** — the
touchpoint is deferred until the verdict gap is closed (and, per the
LEDGER-002 owner requirement, warning parity is measured).

## Decision

1. **mt-022 (precise per-node relevant-type propagation) runs now**, as a
   rung-gating bead: implement the reference's precise bounding-type
   computation and true top-down resolve pass, re-enable every tightening
   ADR-0009 reverted (illegal joins, ambiguous names, ambiguity-suppressed
   sort/arity, bad calls, the narrow structural rejects), and re-run the
   mt-020 gauge to convergence. Target: 100% alloy4fun agreement; any
   irreducible remainder must be individually triaged, tiny, and explained —
   an honest 99.99% with named corners beats a fudged 100%.
2. **mt-023 (warning parity + `--strict`) follows immediately** — the
   relevance-warning classes it needs fire inside mt-022's precise pass.
3. **The Rung-2 owner touchpoint happens after both**, presenting the final
   verdict-agreement and warning-parity numbers alongside the `mettle check`
   build. LEDGER-003 is re-proposed with the new numbers at the same time.

## Consequences

- Rung 3 (solving) starts later; correctness-first was the project's stated
  discipline and the owner has priced the delay.
- ADR-0009's accept-lean *bias* remains the interim rule inside mt-022's
  development loop (never wrongly reject while precision is being built);
  it is retired class-by-class as each tightening lands with clean gauge runs.

## Alternatives considered

- **Touchpoint now, precision later** (the ADR-0009 schedule): rejected by the
  owner — testing effort is better spent once verdicts are trustworthy.
