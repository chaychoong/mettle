# ADR-0017 — Gauge default budgets: encode 32M × conflicts 10k, chosen on a measured paired-knob frontier

**Status:** Accepted (tech-lead decision under the STATE.md chunk mandate; zero-regression measured) · **Date:** 2026-07-28 ·
**Beads:** mt-078 (the capacity census that isolated the knobs), mt-079 (this measurement + the change)

## Context

The mt-078 census classified all 179 capacity/over_budget defer rows and, along
the way, isolated the two budget knobs one at a time on full-corpus sweeps:
raising **encode alone** 4M→32M bought +46 agreements at 2.2× wall with zero
regressions, while raising **conflicts alone** 10k→100k bought +19 at 4.6× wall
with one instructive regression — `leader_events[3]` flipped
over_budget→capacity because the extra conflicts let the temporal step-sweep
reach a longer trace length that blew the *unraised* 4M encode ceiling. The
lesson filed with the census: **the knobs interact; never move one without
measuring the pair.**

The standing default (encode 4M) dated from mt-049, whose comment recorded "8M
timed out past 40 min" — a measurement taken *before* the mt-054..059
throughput campaign (command-level parallelism, baseline-before-enumerate,
ADR-0013) rebuilt the instrument. That finding no longer binds.

This ADR is the paired measurement the census called for. Grid: encode pinned
at 32M × conflicts {10k, 25k, 50k}, full corpus, `--jobs 8`, strictly
sequential runs on a quiet machine (wall time is the decision metric), each
diffed row-by-row against a same-day fresh defaults baseline.

## The measured frontier

| point | conflicts | encode | agreements | Δ vs defaults | wall | × wall | regressions |
|---|---|---|---|---|---|---|---|
| defaults | 10k | 4M | 356 | — | 261s | 1.0× | — |
| **A (chosen)** | **10k** | **32M** | **402** | **+46** | **583s** | **2.2×** | **0** |
| B | 25k | 32M | 408 | +52 | 977s | 3.7× | 0 |
| C | 50k | 32M | 416 | +60 | 1906s | 7.3× | 0 |

DISAGREE 0, panics 0, self-check failures 0 in every run; 564/564 commands,
identical row sets. The census's interaction flip does **not** reproduce
anywhere in the grid — raising the encode ceiling first removes the condition
that caused it (`leader_events` rows are byte-identical across all four runs).

The marginal shape is decisive: point A captures 46 of the 60 agreements
available anywhere on the grid for +322s; B's further +6 costs +394s and C's
further +8 costs another +929s — superlinear wall for single-digit gains.
The non-agreement movement is bucket-neutral shuffle: 22 rows (all
`correctChord.als` plus `ertms_1A[9..13]` and `fullsub2[0]`) move between
capacity/over_budget/jar_nonverdict without touching an agree bucket, and
`correctChord` cannot agree at *any* mettle budget until its jar baseline is
banked deeper (census finding, unchanged).

## Decision

1. **`solve-gauge` defaults become `--encode-budget 32000000 --conflicts
   10000`** (conflicts unchanged). The sweep-baseline artifact
   (`baselines/corpus-sweep-sb20.json`) is re-captured under the new regime so
   schedule costs and `--delta` bases match.
2. **The pairing rule is standing:** any future change to either budget default
   must re-measure the pair on a grid, not the knob in isolation. The hazard is
   concrete and probe-pinned (the temporal step-sweep interaction above).
3. Conflicts stay at 10k **as a default**. The measured route to the remaining
   over_budget rows is not more conflicts at 7× wall; it is the census's attack
   order — closure-encoding cost work (family C), deeper oracle-side banking
   (correctChord, family E) — with deep-budget runs staying an explicit
   per-run flag, exactly as before.

## Consequences

- The scorecard's "at defaults" regime changes: agreements 356→402, sweep wall
  ~4.5→~10 min at `--jobs 8`. STATE.md's scorecard prose is re-baselined from
  fresh runs (stage 1 + both count nets) in the same chunk. Measured at the
  re-baseline: the fresh no-flag stage-1 run is row-identical to grid point A;
  both count nets stay **COUNT_MISMATCH 0**, SB-0 count_match holds at 56, and
  SB-20 count_match rises 79→84 (the deeper encode ceiling lets five more
  enumerations complete instead of skipping).
- ADR-0013's principle is upheld in the direction it cares about: this trades
  *speed for coverage* (more real verdicts per sweep), never coverage for
  speed. Iteration-speed practice is unchanged — `--only`/delta/fail-fast for
  inner loops, full sweeps at chunk level.
- The mt-049 comment in `solve_gauge.rs` is rewritten in place; its
  measurement is superseded, and the new comment carries the pairing rule.

## Alternatives considered

- **B or C (25k/50k conflicts).** Rejected on the frontier: +6/+14 agreements
  over A for +1.5×/+5× additional wall. The rows they convert are
  search-bound (census family D territory) — solver-quality work, low yield,
  deliberately deprioritized in the census attack order.
- **Encode higher than 32M (census L2 = 128M).** Not measured here as a
  default candidate: the census showed family B (the 22 rows that need L2)
  comes with families C/D staying stuck regardless, and L2 file-cap blowups
  made even the census resort to per-command probing. 32M is the census's own
  "floor with zero regressions" recommendation; deeper stays a per-run flag.
- **Leaving defaults alone.** Rejected: the instrument was leaving 46 measured,
  regression-free agreements on the table to defend a wall-time finding
  (mt-049's 40-minute 8M sweep) that predates the throughput campaign by three
  ADRs.

## Amendment (mt-082, 2026-07-29): conflicts re-paired to 25k after the ADR-0018 encoder reshape

The pairing rule turned out to bind sooner than expected, and not through a
budget knob: [ADR-0018](0018-encoder-structural-sharing.md)'s structural
sharing changed the CNF shape, moving five rows across the conflict-budget
boundary and roughly halving the wall cost of conflicts (stage-1 588s→478s).
Re-measuring the conflicts axis on the new encoder (10k/25k/50k at encode
32M, same discipline as the original grid):

| point | agreements | Δ vs 10k | wall | × wall | regressions |
|---|---|---|---|---|---|
| 10k | 421 | — | 478s | 1.0× | — |
| **25k (new default)** | **428** | **+7** | **773s** | **1.62×** | **0** |
| 50k | 435 | +14 | 1259s | 2.63× | 0 |

DISAGREE 0 everywhere. The original decision's 25k rejection (+6 at 3.7×)
no longer describes the instrument: the same point now costs 1.62× and its
seven conversions include both recoverable ADR-0018 boundary rows
(`ringlead[2]`, `etl_scd[5]`). **The default becomes conflicts 25k × encode
32M.** 50k stays a per-run flag — its further +7 pushes the three-net
battery near an hour, past the chunk-level cadence the instrument serves.
The three durable ADR-0018 losses (`OLAPUsagePrefs[0]`,
`elevator_spl_events[29]`, `life.als[1]`) remain over_budget even at 50k
and are family-D solver-quality work, deprioritized per the census.

The rule itself is sharpened by this episode: **re-pair the knobs whenever
either budget default changes OR the encoder's CNF shape changes.** The
defaults comment in `solve_gauge.rs` now says so.

## Second amendment (mt-087, 2026-07-29): the corner point 100k × 64M after gate-level sharing

mt-087's gate cache reshaped the CNF a second time (correctChord −79.9%
clauses; sweep wall −70%), so the rule fired again — this time on a full
two-axis grid, because mt-086 had banked the exact encode-spend
thresholds of the 28 remaining capacity rows (the 8 cheapest sit at
~48–51M, inside a 64M ceiling). All points fresh, `--jobs 8`, row-diffed
against the incumbent B = 25k×32M (agree 458):

| point | conflicts × encode | agree | Δ vs B | wall | regressions |
|---|---|---|---|---|---|
| A | 10k × 32M | 450 | −8 | 139s | 8 |
| B (incumbent) | 25k × 32M | 458 | — | ~330s | — |
| C | 50k × 32M | 465 | +7 | 344s | 0 |
| D | 100k × 32M | 476 | +18 | 614s | 0 |
| E | 25k × 64M | 466 | +8 | 324s | 0 |
| **F (new default)** | **100k × 64M** | **484** | **+26** | **699s** | **0** |

DISAGREE 0, self-check 0, panics 0 at every point. F's row moves are
**exactly the union** of D's and E's — the two axes touch disjoint
buckets (conflicts converts over_budget rows, encode converts capacity
rows), so the corner is purely additive. D's 18 include
`ceilingsAndFloors[4]` (mt-087's one disclosed regression, recovered),
`life[1]` and `handshake[0]` (family-D rows the census deprioritized —
the smaller CNF moved them into reach), and `correctChord[9]/[10]`. E's 8
are precisely the TransForm rows mt-086's thresholds predicted.

**The defaults become conflicts 100k × encode 64M.** The wall argument
that capped the last two amendments inverted: gate sharing made conflicts
~2× cheaper and each conflict more productive, so the corner's 699s costs
the same absolute wall as the pre-sharing 25k×32M default (~650s) while
carrying +26 agreements. The remaining over_budget 47 and capacity 20 are
genuinely deeper water (capacity's floor is correctChord[0..5] at ~89M
true spend and TransForm's 14 big rows at ~190M+).
