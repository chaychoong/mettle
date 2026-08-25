# Roadmap

## North Star
**mettle is a drop-in replacement for the latest Alloy. It does everything Alloy does, exactly.**
The single measure is the **conformance scorecard**: the percentage of real Alloy models where mettle's verdict (and, where applicable, model count) matches the reference Alloy 6 jar. When the scorecard reaches 100% across feature areas, "drop-in" becomes a measured fact.

We measure the "exactly" claim with the scorecard and we disclose the remaining gap in [LIMITATIONS.md](../LIMITATIONS.md). That gap shrinks over time.

## The human-testable rungs
Each rung is something the product owner can run by hand and judge. The tech lead does the plumbing between rungs silently, then surfaces at each rung with a build and one thing to look for.

| Rung | "You can now…" | How you judge it |
|------|----------------|------------------|
| **1. It reads my Alloy** | `mettle check model.als` accepts real files or points at the exact error, better than Alloy | Throw your ugliest models at it; is the parse rate high and are errors clearer? |
| **2. It catches my mistakes** | Type/name errors flagged, with the same accept/reject decisions as Alloy | Feed models you know Alloy accepts/rejects; does it agree? |
| **3. It actually solves my models** | `mettle run` / `check` returns a correct instance or "no counterexample," self-verified | Run a real model; compare the verdict to Alloy |
| **4. It agrees with Alloy across everything I have** | Supported set covers integers, ordering, cardinality; scorecard climbs | Run your whole collection; watch the % agreement; step through instances and compare counts |
| **5. It feels like a real tool** | One-command install; evaluator REPL; Sterling visualization (`mettle serve`) | Fresh-install → visualized instance in under a minute, no docs |
| **6. It does time** | Temporal Alloy 6 (`var`, `always`/`eventually`, traces) for bounded checks | Run your temporal models; confirm bounded checks agree with Alloy |

**Status (2026-07-28): all six rungs are exited.** Rungs 1 to 4 closed at their per-rung gates, with histories in [TASKS.md](TASKS.md) and the [ADR index](adr/). Rungs 5 and 6 were blessed together at the **combined feature-complete review** of v0.1.0 ([REVIEW-v0.1.0.md](REVIEW-v0.1.0.md)), where all parts passed and Rung 6's blessing made [ADR-0015](adr/0015-rung6-temporal-architecture.md) Accepted. The open goal is the North Star itself: **measured drop-in parity**. The distance left is the scorecard's remainder (capacity and budget defers) plus [LIMITATIONS.md](../LIMITATIONS.md). Versioning is deliberately zero-based (owner, 2026-07-28): mettle stays on 0.x, with minor bumps for milestones and patches for fixes, and reaching drop-in is announced by the scorecard. There is no 1.0.0 release planned to mark it.

## Mapping to the internal phases (plan §6)
- Pre-Rung-1 (Phase 0): oracle harness, scaffolding, and steering docs.
- Rung 1 = Phase 1 (syntax). Rung 2 = Phase 2 (names and types). Rung 3 = Phase 3 (relational core, vertical slice). Rung 4 = Phase 4 (integers, symmetry breaking, counting, candid reporting). Rung 5 = Phase 5 (experience). Rung 6 = Phase 6 (temporal solving).

**Sequencing rule:** any rung may ship early and rough if the scorecard holds. No rung closes with an unexplained scorecard regression.
