# ADR-0021 — The volume lever: cut the own CDCL's propagation volume (trail saving → shrink → tier retention)

**Status:** Accepted (tech-lead decision, 2026-08-19)
**Date:** 2026-08-19
**Builds on:** [ADR-0020](0020-cdcl-clause-db-reduction.md) (whose stage-0 profile measured the mechanism this ADR attacks, and whose staged-landing discipline this ADR reuses), [ADR-0017](0017-gauge-default-budgets-paired-frontier.md) (the pairing rule the final stage triggers), [ADR-0019](0019-optional-cadical-backend.md) (the cross-backend instrument that is this campaign's standing acceptance closer).

## Context

mt-092 closed at agree 502 (250k×64M defaults, DISAGREE 0) by making the
existing search trajectory cheaper to execute. What it deliberately did not
touch is the trajectory's **volume**: ADR-0020's stage-0 profile measured that
the solver re-propagates ~100× more than it should per conflict — 477/1,932/
13,429 trail pops per conflict on the three calibration rows, tracking
**post-minimization learned-clause length** (34/74/126 literals) monotonically
— and that the arithmetic ceiling of pure execution engineering is 5.8–8.2×,
below what the durable tail needs. The mt-092 closing cross-run sharpened the
target: **CaDiCaL answers 22 of the 24 durable `over_budget` rows within the
same 1M conflict budget on identical CNFs** (unknown only on fullsub2[0] and
correctChord[13]), so what separates the two solvers on the tail is search
quality — fewer/cheaper re-propagations and better clause retention — not
encoding and not raw visit cost.

What the solver has today (verified in code, per ADR-0020's revision-note
discipline): recursive learned-clause minimization (`minimize`/`lit_redundant`,
a measured 3.0× length cut), LBD-based `reduce_db` that keeps the better half
ranked by **static** LBD (computed once at learn time, never refreshed) with a
lowest-`ClauseRef` tie-break, Luby restarts, phase saving, blocking literals,
a flat clause arena, and an indexed max-heap decision order. There are no
retention tiers, no clause-use signal, no shrinking beyond minimization, and
backjumps discard the popped trail wholesale — every redescent re-derives it
through `propagate`, which is exactly the measured 100× volume.

A commissioned technique survey (sonnet delegate, 2026-08-19; sources: Fleury &
Biere SAT 2021, Hickey & Bacchus SAT 2020, Oh's COMiniSatPS thesis + CaDiCaL
`reduce.cpp`/`options.hpp`, Nadel & Ryvchin SAT 2018, Luo et al. IJCAI-17,
Han & Somenzi SAT 2009) mapped the practice space against our constraints.
Its parameter values were machine-extracted and are treated as *reported, to
be re-verified at implementation*, not as pinned facts.

## Decision

mt-093 lands the volume lever as **three single-technique stages, each judged
on its own full row-diffed sweep**, then ONE ADR-0017 paired-grid re-pair and
the deep-tail cross-run as the closing acceptance item — the mt-092 shape,
reused because it worked twice.

**Stage 1 — trail saving on backtrack** (Hickey & Bacchus, SAT 2020). On
backjump, keep the popped trail suffix; on redescent, replay a saved literal
(with its saved reason) whenever the replay is consistent with current
assignments and the saved reason clause is still live, falling back to normal
`propagate` on any mismatch. This attacks the measured defect head-on: the
100× volume is re-propagation after backjumps. The survey claims the technique
is trajectory-neutral by construction (backtrack-level selection is
unchanged). **The tech lead does not accept that claim as stated** — a
replayed literal can carry a different reason than fresh propagation would
assign, and reasons feed conflict analysis, so learned clauses can differ.
Stage 1 therefore runs predictions-first, mt-092-style: the *preferred*
outcome is a byte-identical sweep + identical conflict counts + lower wall
(stage-1a-of-mt-092 acceptance); if the sweep moves, the stage is
**reclassified as a disclosed search change** and judged like stage 1b was
(full row-diff, zero verdict flips, recoverable regressions disclosed) — or
reverted if the row-diff is net-negative. Scored prediction: trajectory
byte-identical (confidence medium); calibration-row walls −1.3× to −2.5×.

**Stage 2 — all-UIP learned-clause shrinking** (Fleury & Biere, SAT 2021;
Kissat `shrink.c`). A second pass after the existing recursive minimization:
group the learned clause's literals by decision level and, per level (highest
first), resolve within the block along the trail; if the block collapses to a
single level-local UIP, that literal replaces the block. Structurally additive
to minimization (its authors design it as exactly this second pass); bounded
trajectory effect (only removes literals via valid resolution — the backjump
can only stay equal or deepen). A disclosed search change from the start, own
sweep, own row-diff. Scored prediction: post-minimization mean length −10–30%
on the calibration rows, pops/conflict down commensurately; net agree −2…+4
at the standing defaults before any re-pair.

**Stage 3 — tier-based clause retention** (Oh's core/tier2/local; CaDiCaL's
production variant). Replace keep-better-half with: a **core** tier (LBD ≤ T1)
never deleted, a **tier2** (T1 < LBD ≤ T2) kept while recently used, a
**local** tier reduced aggressively — with LBD refreshed on use (the current
static-LBD ranking is the survey's clearest gap vs practice) and all
thresholds/cadences integer- and conflict-count-driven on total orders.
Permanent/locked/blocking/config clauses stay exempt exactly as `reduce_db`
exempts them today. The largest lottery exposure of the three stages, taken
last so stages 1–2 are already banked and attributable. Scored prediction:
conflicts-to-proof on deep-UNSAT calibration rows −1.2× to −2×.

**Then:** ONE paired-grid re-pair (the ADR-0017 rule fires on solver
search/wall changes — extended at mt-092), and the mt-092 closing cross-run
configuration (`backend-instrument --cross`, own arm 1M, CaDiCaL check) as the
standing final gate. Any verdict split anywhere = STOP THE LINE.

**Yield estimate (scored at the re-pair, ADR-0020 discipline):** base **+5**
at re-paired defaults (the five measured 1M conversions brought into a
re-paired default by wall-side gains alone), upside **+12** if the
search-quality stages cut conflicts-to-proof on the chord/handshake/lc-lenses
families. Explicitly out of scope: the 20 `capacity` rows (encode-bound; a
different lever) and fullsub2[0]/correctChord[13] (the rows even CaDiCaL
cannot answer at 1M — quoted as genuinely hard, LIMITATIONS territory).

## Stage-1 outcome (2026-08-19, addendum — REJECTED by measurement, reverted)

Trail saving was implemented in full (opus delegate, predictions-first;
tech-lead reviewed the diff and independently re-ran tests/clippy), measured,
and **reverted the same day on the full row-diff: agree 502 → 500** (3
conversions vs 5 regressions at the standing defaults; DISAGREE 0,
self-check 0, panics 0 throughout — correctness was never at risk). Two model
corrections come with the rejection, both now load-bearing for the remaining
stages:

1. **This ADR's stage-1 mechanism claim was wrong.** The published algorithm
   never advances the propagation head past replayed literals (doing so would
   be unsound), so trail saving cannot cut the §(b) re-propagation volume; its
   only direct saving is early conflict detection, which a replay-off control
   measured at ~0 (6 of 2,333 / 20 of 139,624 conflicts). The −73%/−18%
   calibration conflict drops were trajectory lottery — and the corpus-wide
   lottery nets negative.
2. **The survey's trajectory-neutrality claim is disproven** for this solver,
   as this ADR suspected: replayed literals land at the current level in saved
   order with saved reasons, all three of which feed `analyze`.

The stage's yield-irrelevant residue is banked: the implementation survives as
`scratchpad/probe/mt093/stage1-trail-saving.patch` (with A/B artifacts and
NOTES), and the newly documented `lits[0]`-across-backjumps hazard binds any
future technique that holds reasons across a backjump. **Stages 2 (shrink) and
3 (tier retention) proceed unchanged** — their mechanisms (clause length,
retention) are the measured §(b) channel, not this one — and the yield
estimate stands, now resting entirely on them.

## Constraints (inherited from ADR-0020, restated as binding)

1. Determinism by construction: every new order (saved-trail replay order,
   shrink block order, tier ranking) is a total integer order; no timing, no
   hash-map iteration near the search.
2. Blocking/config/reason clauses stay permanent and locked; COUNT_MISMATCH 0
   on both nets is a per-stage gate. Trail saving must invalidate saved
   entries whose reason clause was tombstoned by `reduce_db`.
3. Effort semantics unchanged: `effort()` keeps meaning conflicts.
4. One technique per stage, never bundled; each stage's sweep names it.
5. Instance re-pins expected and disclosed on trajectory-changing stages
   (ADR-0020 constraint 6 verbatim).
6. Incremental-solve correctness: the enumeration seam re-enters `solve` with
   added clauses; saved trails and tier state must survive or reset across it
   — decided per stage, asserted by the enumeration tests.

## Consequences

- The campaign continues on the measured mechanism with the same staged,
  attributable discipline that took 484→502; each stage is individually
  revertible on a net-negative row-diff.
- The durable tail stops being "the solver is slow" and becomes "the solver's
  search is weaker than CaDiCaL's on these 24 rows" with a per-stage
  measurement of the gap closing (pops/conflict, learned-clause length,
  conflicts-to-proof on the calibration trio).
- Risk honestly stated: stages 2–3 are conflict-count lotteries (mt-092
  stage 1b turned a 0.12s row into a defer; the re-pair recovered it). The
  row-diff + disclosed-regression discipline is the mitigation, and the
  final re-pair is where the yield is actually banked.

## Alternatives considered

**Chronological backtracking (Nadel & Ryvchin) / lazy reimplication.**
Rejected for this bead: the most invasive option surveyed — it breaks the
trail-order-equals-level-order invariant the whole solver assumes, carries
the largest lottery exposure, and its stated goal (cut re-propagation after
backjumps) is what stage 1 achieves without changing backtrack semantics.
Reconsider only if stages 1–3 leave a residual gap that profiling attributes
specifically to deep narrow backjumps.

**Learnt-clause vivification (Luo et al.).** Deferred, not rejected: real
evidence on exactly our metric, but the largest build cost (a second
propagation routine + tick budgeting) and a direct interaction with the
permanent-clause constraint. Re-profile the residual gap after stage 3 and
spec it then if the length signal still dominates.

**On-the-fly subsumption (Han & Somenzi).** Rejected: overlaps the existing
recursive minimization's redundancy mechanism; expected marginal yield too
low to spend a stage on.

**Adopt CaDiCaL for the tail instead.** Already owner-decided the other way
(ADR-0019): the own CDCL stays default and yardstick because its determinism
underpins the counting nets. This ADR is the continuation of that posture.

**Park the campaign at 502.** Rejected while a measured, determinism-
compatible mechanism with a 22-of-24 proven-answerable target remains;
parking stays the fallback if the stage row-diffs disappoint.
