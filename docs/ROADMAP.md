# Roadmap

## North Star
**mettle is a drop-in replacement for the latest Alloy — it does everything Alloy does, exactly.**
The single gauge is the **conformance scorecard**: the % of real Alloy models where mettle's verdict (and, where applicable, model count) matches the reference Alloy 6 jar. When the scorecard reaches 100% across feature areas, "drop-in" is a measured fact.

We never *claim* "exactly." We *measure* it (scorecard) and we *disclose* the gap ([LIMITATIONS.md](../LIMITATIONS.md)), which shrinks over time.

## The human-testable rungs
Each rung is something the product owner can run by hand and judge. The tech lead does the plumbing between rungs silently and surfaces at each rung with a build + one thing to look for.

| Rung | "You can now…" | How you judge it |
|------|----------------|------------------|
| **1. It reads my Alloy** | `mettle check model.als` accepts real files or points at the exact error, better than Alloy | Throw your ugliest models at it; is the parse rate high and are errors clearer? |
| **2. It catches my mistakes** | Type/name errors flagged — same accept/reject decisions as Alloy | Feed models you know Alloy accepts/rejects; does it agree? |
| **3. It actually solves my models** | `mettle run` / `check` returns a correct instance or "no counterexample," self-verified | Run a real model; compare the verdict to Alloy |
| **4. It agrees with Alloy across everything I have** | Supported set covers integers, ordering, cardinality; scorecard climbs | Run your whole collection; watch the % agreement; step through instances and compare counts |
| **5. It feels like a real tool** | One-command install; evaluator REPL; Sterling visualization (`mettle serve`) | Fresh-install → visualized instance in under a minute, no docs |
| **6. It does time** | Temporal Alloy 6 (`var`, `always`/`eventually`, traces) for bounded checks | Run your temporal models; confirm bounded checks agree with Alloy |

## Mapping to the internal phases (plan §6)
- Pre-Rung-1 (Phase 0): oracle harness + scaffolding + steering docs.
- Rung 1 = Phase 1 (syntax). Rung 2 = Phase 2 (names & types). Rung 3 = Phase 3 (relational core, vertical slice). Rung 4 = Phase 4 (integers, symmetry breaking, counting, honesty). Rung 5 = Phase 5 (experience). Rung 6 = Phase 6 (temporal solving).

**Sequencing rule:** any rung may ship early and rough if the scorecard holds; no rung closes with an unexplained scorecard regression.
