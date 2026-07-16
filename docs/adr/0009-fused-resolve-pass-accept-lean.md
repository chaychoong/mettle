# ADR-0009 — Fused resolve pass and the accept-lean interim posture

**Status:** Accepted · **Date:** 2026-07-16 · **Beads:** mt-018 (decision made
at its merge), mt-020 (measures the consequences) · **Amends:** [ADR-0008](0008-rung2-resolver-architecture.md)
(decision 4; the rest of ADR-0008 stands unchanged)

## Context

ADR-0008 decision 4 prescribed two explicit passes (bottom-up bounding types,
then a separate top-down disambiguation walk), listing a fused bidirectional
walk under "alternatives considered / rejected". mt-018 delivered the resolver
as a **single fused walk**: children are fully typed bottom-up before their
parent resolves its own overload choice against the relevant type pushed from
above (`resolve/expr.rs`, the `Want` type). The ADR's stated correctness
invariant — every candidate's finished type exists before a choice is made —
holds; what is lost is the reference's *complete* second pass, in which an
unresolved `ExprChoice` at the very top still gets one full retry and then
errors.

Consequences observed at merge (jar-probed, tech-lead verified):

- **Ambiguous 0-ary names lean accept.** `fun g: A {…}` + `fun g: B {…}` +
  `fact { some g }`: the jar REJECTS ("This name is ambiguous"); mettle picks
  the first minimum-weight candidate and ACCEPTS. Call-form ambiguity
  (probe 15) still rejects.
- **`ArityMismatch` is suppressed** when the enclosing formula involved an
  ambiguous pick, avoiding false rejects from leniently-picked wrong-arity
  candidates.
- The `type == EMPTY iff errors` invariant (ADR-0008 decision 5) does not hold
  literally on accept-lean paths (unresolved names may resolve to `univ`), so
  the `debug_assert` is documented intent, not asserted.

## Decision

1. **Accept the fused walk** as the shipped mt-018 structure. It is
   accept/reject-equivalent to the two-pass design everywhere except top-level
   choice exhaustion, dramatically simpler, and the invariant that motivated
   two passes is preserved.
2. **Accept the accept-lean posture as an explicitly interim state**, recorded
   in LIMITATIONS. The lean direction is deliberate: mettle must never wrongly
   *reject* a real model (the drop-in promise); wrong *accepts* are measurable
   divergences the mt-020 differential gauge will surface with real
   frequencies.
3. **mt-020 decides the tightening.** If the alloy4fun differential shows
   jar-rejects-ambiguous/mettle-accepts at any meaningful rate, mt-018's walk
   gains the reference's full top-down retry-then-error pass (the ADR-0008
   shape) for choice nodes — a bounded, local extension of `expr.rs`, not a
   rewrite. The suppressed-`ArityMismatch` heuristic is re-examined at the same
   time.

## Consequences

- Rung 2 can proceed to mt-019/mt-020 without a speculative rewrite; the gauge,
  not taste, decides how much of the second pass is needed (ROADMAP sequencing
  rule: ship rough if the scorecard holds).
- LIMITATIONS carries the honest divergence list until then: ambiguous-name
  over-acceptance, ambiguity-suppressed arity errors, lenient meta-`$` models,
  partial §5.2 warning catalog.
- Anyone touching `resolve/expr.rs` must preserve the bottom-up-before-choice
  invariant and the accept-lean bias direction until mt-020 rules.

## Alternatives considered

- **Demand the two-pass rework now.** Rejected: costs an opus-scale rewrite
  before any measurement exists; the parser rungs proved the
  ship-then-differentially-tighten loop (mt-011 → mt-013/mt-014) is faster and
  ends at the same fidelity.
- **Keep the deviation as a report footnote.** Rejected: ADR-0008 is a binding
  Accepted decision; deviating from it silently would rot the decision trail.
