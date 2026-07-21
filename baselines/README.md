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

## portus-63-verdict.json (2026-07-17, mt-037)

158 commands / 63 model files (+deps): **45/48 expect-matches, 3 mismatches,
10 file timeouts, 0 errors.**

Triage (2026-07-17, tech lead):
- **3 mismatches** (`dijkstra-2-process.als` ShowDijkstra, `peterson.als`
  TwoRun/ThreeRun): portus vendors copies of the same upstream models already
  triaged above — same stale expects, the jar's UNSAT is the oracle.
- **10 timeouts** at 60s (fullsub2, mesh, serializableSnapshotIsolation,
  lc-lenses, ertms_1A, elevator_spl_events, HotelVar, correctChord, and the two
  TransForm `util/` minimality scripts): genuinely large problems; no verdict
  cached, so the solve gauge reports their commands as `no_baseline`.

## Count baselines: `*-count-sb<N>.json` (2026-07-21, mt-054)

Cached reference-jar **model counts** at a pinned config, so `solve-gauge
--count` no longer pays a live JVM per file per sweep (the counts are immutable
facts; ADR-0002's SB-0 remains the counting yardstick, SB-20 the mt-048 net).
Each file carries a `config` header (`count_symmetry`, `count_cap`,
`jar_timeout_secs`, `no_overflow`, `solver`); the gauge hard-errors on a
meaning-bearing mismatch and warns on a `jar_timeout` difference. A command
missing from every loaded baseline is a typed `skip_no_count_baseline`;
`--live-jar` restores the live JVM path.

Captured 2026-07-21 via `solve-gauge --refresh-counts` at the gauge defaults
(cap 10000, forbid overflow, sat4j, 300s/file): `alloytools-models-count-sb0/
sb20.json` (94 files each) + `portus-63-count-sb0/sb20.json` (73 files each).
The `*-slow-count-sb0.json` supplements re-capture the four 300s-boundary files
at 900s (chordbugmodel ×2 converted to counts; ceilingsAndFloors + life still
time out — the SB-0 net's 3 standing `skip_jar_timeout` commands). Loaded files
merge in sorted name order, later file wins per relpath — which is why the
`-slow-` supplements override.

Verified 2026-07-21: the cached SB-0 net reproduces the live-era mt-048 results
exactly (count_match 49, COUNT_MISMATCH 3 = the mt-041 family, all skips
identical); the SB-20 net likewise (71 / 6 = mt-041 ×3 + mt-055). Refresh
commands, one per corpus/config, ~2h40m total on the 2-core VM:

    solve-gauge --refresh-counts baselines/<corpus>-count-sb<N>.json \
      --count-symmetry <N> --resume <corpus-root>
