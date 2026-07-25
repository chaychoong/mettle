# ADR-0014 — A thin Rung-5 slice (the evaluator REPL) before Rung 6

**Status:** Accepted (owner-delegated 2026-07-25 — "do what you think is best")
· **Date:** 2026-07-25 · **Beads:** mt-061 (pinned evaluator contract),
mt-062 (the REPL itself)

## Context

Rung 4 closed on 2026-07-25 (ADR-0012 §7). Two rungs were unblocked and
independent: **Rung 5** ("it feels like a real tool": one-command install,
evaluator REPL, Sterling visualization) and **Rung 6** ("it does time":
temporal Alloy 6 — `var`, `always`/`eventually`, traces). The sequencing was a
genuine owner scope call, surfaced with tradeoffs in STATE.md (2026-07-25):

- **Rung 6 is what the North Star measures.** The conformance scorecard is the
  one gauge; Rung 5 does not move it at all, while 22 corpus commands sit in
  `lower:temporal` and temporal is the defining feature of Alloy *6*. But it is
  the largest remaining semantic push — a new solving regime (trace unrolling,
  loop detection), new scope surface (`steps`), its own conformance campaign —
  with a long stretch where the owner cannot judge progress by running
  anything.
- **Rung 5 is what makes the owner able to find bugs at all.** Today the only
  hand-exercise channel is `mettle exec`. An evaluator REPL opens a
  qualitatively different channel — *use* — and it is low-risk, mostly additive
  over an evaluator that already exists (`als-core::eval`, differentially
  tested against the encoder as a matched pair since mt-044).

The owner delegated the call rather than choosing ("do what you think is
best"), which makes the standing tech-lead recommendation the decision.

## Decision

**Build the evaluator REPL first — nothing else of Rung 5 — then start
Rung 6, then return for the rest of Rung 5** (install polish, `mettle serve` /
Sterling).

The REPL is the cheapest high-value piece of Rung 5 and it is a **debugging
multiplier for Rung 6**: temporal work means staring at trace instances, and
an interactive "evaluate this expression against this instance" loop is
exactly the instrument that work needs. Building it first pays for itself
rather than competing with Rung 6. It also gives the owner something concrete
to hold before the long temporal stretch.

Contract-first, as at every rung (mt-016, mt-043 pattern): the jar's evaluator
behavior is pinned by probes into the reference docs **before** implementation
(mt-061), and the REPL implements from the pinned contract, never from vibes.
Conformance target: an expression evaluated in mettle's REPL against an
instance must render the same value the jar's evaluator renders against the
same instance — divergences are LIMITATIONS entries like any other.

## Consequences

- The scorecard does not move during the slice. This is deliberate and
  disclosed: the slice is bounded at two beads, and Rung 6 (the scorecard's
  remaining 22 temporal defers) starts immediately after.
- `mettle exec` grows an interactive mode; the exec/REPL seam must not disturb
  the deterministic pipeline (STYLE D1 — the REPL is a consumer of solved
  instances, never a mutation of how they are produced).
- The rest of Rung 5 (install, Sterling) is explicitly NOT started; ROADMAP's
  Rung-5 row stays open until those land after Rung 6.
