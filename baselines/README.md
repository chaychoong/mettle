# Oracle baselines

Cached reference-jar verdicts over the local corpora, produced by
`conform --json-out <file>.json <corpus-dir>` at the ADR-0002 pinned jar and
the LEDGER-001 defaults (symmetry 20, noOverflow=true, sat4j, 60s timeout).
These are the jar's answers mettle must eventually match; re-run any time —
`corpus/` itself is reproducible via `scripts/fetch-corpora.sh`.

## alloytools-models-verdict.{json,txt} (2026-07-15)

234 commands / 94 files: **91/94 expect-matches, 3 mismatches, 7 errors, 1 timeout.**

Triage (2026-07-15, tech lead):
- **3 mismatches** (`dijkstra.als` ShowDijkstra, `peterson.als` TwoRun/ThreeRun):
  `expect 1` but the jar itself answers UNSAT — verified NOT overflow-related
  (same verdict with `--allow-overflow`). Stale upstream expects; the jar's
  verdict is the oracle, the expect annotation loses (ADR-0002 Net 0 is a
  cross-check, not ground truth).
- **7 errors**: `s_ringlead.als` (×4) and `ins.als` — "requires higher-order
  quantification that could not be skolemized" (genuine engine limitation);
  `trash.als` (×2) — "Bounded engines do not support complete model checking"
  (unbounded `1.. steps` check needs an unbounded engine like electrod, out of
  scope for the sat4j configuration).
- **1 timeout**: `temporal/buffer.als` at 60s.

When mettle solves, the comparison set is the 234 per-command verdicts in the
JSON, not just the expect subset.
