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

## Sweep baselines: `*-sweep-sb<N>.json` (mt-057)

Unlike everything else here, this artifact records **mettle's own** last known
sweep, not the jar's answers: per command (`relpath[idx]`) the verdict bucket,
the counting bucket when stage 2 ran, and an advisory wall time in
milliseconds. `N` is the **stage-1** symmetry cap. One artifact drives both
mt-057 uses, so they can never disagree with each other:

1. **Longest-processing-time-first scheduling.** The recorded per-command times
   sort the work queue descending, so the tail starts first. Times are
   *scheduling hints only*: they never enter the report, and reordering provably
   cannot move a byte because results fold in item position (file-sorted,
   index-ascending), never completion order.
2. **Deltas (`--delta`).** Diffs the run against the artifact and reports what
   moved (`changed` / `new commands` / `gone commands`) instead of re-deriving
   the previous state.

**Neither costs any coverage, so neither needs an opt-in, and the artifact never
decides what the gauge runs — every run sweeps every command.** An earlier
revision of mt-057 did let it skip commands recorded as capacity/over-budget
defers. That was deleted: once command-level parallelism landed, the skip lane
was worth **6%** (3m23s vs 3m35s on the full corpus), which does not buy a lane
that can hide a previously-capped command becoming solvable *and wrong*, or a
new panic on the largest models. `--full` / `--recheck-capacity` survive as
accepted no-op aliases so older recorded commands keep working.

Capture / refresh it with the gauge itself; `--capture-sweep` forces a
non-fail-fast run and stamps the artifact with the current commit:

    solve-gauge --capture-sweep baselines/mettle-sweep-sb20.json --count

A capture is **refused** — nothing is written — if the run did not observe every
command: fail-fast stopped it, or `--only` / `--from-report` / `--from-buckets`
narrowed it. There is no opt-out. The file is committed, so a narrowed capture
outlives the session and no later reader can tell it from a deliberately-narrow
one. Naming a corpus root is *not* a filter — that is how a per-corpus artifact
is captured, and the filename records which.

**Anti-rot.** The `config` header pins `symmetry`, `conflict_budget`,
`encode_budget`, `primary_var_cap`, `no_overflow`, `solver` — plus
`count_symmetry`/`count_cap`/`enum_budget` when the run counts. A mismatch is a
**hard error** whenever the artifact's content can reach the answer, which is
now exactly one consumer: **`--delta`**, whose entire output is a comparison
against these buckets, so diffing across budgets would be a fabricated delta.
Any other run uses the artifact for scheduling hints alone — nothing it says can
reach the report — so there a mismatch is downgraded to "ignored, with a
warning". Otherwise every deep-budget sweep, and the jar smoke test, would fail
on an artifact they were never going to consult.

## portus-63-slow-verdict.json (2026-07-25, mt-050)

Verdict supplement for 8 of the 10 portus files that were file-level 60s
timeouts in `portus-63-verdict.json`: re-captured on the M-series box at
1800s per-file JVM timeouts (HotelVar needed 7200s) — **138 command verdicts**
(mesh 2, lc-lenses 24, both TransForm minimality scripts 36 each, fullsub2 1,
serializableSnapshotIsolation 1, elevator_spl_events 36, HotelVar 2). The
gauge merges this after the base file, and command entries take precedence
over the base file's file-level timeouts.

Triage (2026-07-25, tech lead):
- **1 expect-mismatch**: `elevator_spl_events.als[31]` (`I3a`) — `expect 1`
  but the jar answers UNSAT, in **both** overflow modes (allow-overflow
  re-run verified) — same stale-upstream-expect class as the dijkstra/peterson
  rows above; the jar's UNSAT is the oracle.
- **ertms_1A.als converted at 7200s** (14 commands, 14/14 expect-matches —
  merged into the supplement). **correctChord.als times out at 1800s AND at a final 7200s attempt**
  (2026-07-25, M-series box — no further retries planned; the reference jar
  itself cannot sweep this file's 39 commands in 2h): it stays
  a file-level non-verdict: mettle commands there bucket as `jar_nonverdict`,
  the honest "nothing to compare against" outcome.
