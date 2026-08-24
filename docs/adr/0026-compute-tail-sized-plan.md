# ADR-0026 — The compute tail sized: a measured deep-retry tier converts half of it with zero lottery risk; every solver-internals bet stays owner-gated

**Status:** Proposed (ranking packet; all four options owner-gated — the ADR-0021 campaign close made every further compute-tail route an owner-level decision)
**Date:** 2026-08-24 (sizing bead mt-119; nothing implemented)
**Builds on:** [ADR-0017](0017-gauge-default-budgets-paired-frontier.md) (the paired-frontier defaults this plan deliberately does not move), [ADR-0021](0021-cdcl-volume-lever.md) (the 0-for-3 volume-lever close whose record binds this ranking), [ADR-0019](0019-optional-cadical-backend.md) (the cross-check instrument that pins which rows are answerable at all).

## Context

After mt-118 closed warning parity, the one remaining gap under the owner's
standing "close the gaps first" direction is the compute tail: **49 of 564
solve rows defer at the standing defaults** (250k conflicts × 64M encode,
stage-1 symmetry 20) — 20 `capacity` + 29 `over_budget`, agree 507, DISAGREE 0.
The mt-093 volume-lever campaign closed 0-for-3 against this tail (−2/−2/−6),
so this bead sized the remaining routes before any implementation, from two
commissioned research passes (banked in full at `scratchpad/mt119/{facts,survey}.md`)
plus tech-lead verification of the load-bearing mechanisms.

**What the tail actually is, measured** (sources: the mt-088 census grids
G1/G2/G3, the mt-092 grid points C/D, the mt-092 closing cross-run
`cross-tail29-1M`, and `baselines/*-verdict.json`; all still on disk):

- **`capacity` is the encode-op ceiling, not the var cap.** The bucket is
  `TranslateError::CapacityExceeded` — encoding outgrew the 64M gate-op budget
  (`als-core/src/error.rs`, `encode/mod.rs:571`); the 20k primary-var cap is
  never the trigger on these rows. True spend: correctChord[0..5] ~89M,
  TransForm's 14 rows ~190M+ (post-mt-087 gate sharing).
- **19 of the 20 capacity rows convert to `agree` at 256M encode** — measured
  in the mt-088 G3 grid (100k conflicts × 256M), where they show zero conflict
  sensitivity (bucket-identical between the 250k and 1M conflict points). The
  20th, `tso_minimize[23]`, needs >100k conflicts *on top of* 256M encode; no
  grid point at both >100k conflicts and >64M encode exists anywhere, so its
  exact threshold is unmeasured (expected to convert at 1M×256M, unproven).
- **6 of the 29 over_budget rows convert at 1M conflicts on our own solver**
  (mt-092 grid D: distribution[0], lc-lenses[15], ertms_1A[9], ertms_1A[12],
  elevator_spl_events[18], elevator_spl_events[21]), and correctChord[13]
  additionally becomes a mettle-answers-where-the-jar-can't row at 1M.
- **The durable remainder is 22 rows**, of which 3 (correctChord[13,22,25])
  can never become `agree` — the jar itself has no verdict for them even at
  the 2700s slow-banking tier. Of the durable 22, **CaDiCaL answers 21 within
  a 900s wall on identical CNFs** (all but fullsub2[0], which has no measured
  route on any solver at any probed budget) — the search-quality gap is real
  but confined.
- **Knob interaction hazard, newly flagged from the raw grids:**
  elevator_spl_events[18] is conflicts-bound and *regresses* to over_budget
  at G3's 100k-conflict point despite the 4× encode raise — any deeper tier
  must never lower either axis relative to the defaults.
- **Wall prices** (measured, `mt092grid`/`mt088census` timing logs): full
  564-row sweep 973s at 250k×64M; 3,874s at 1M×64M; 5,116s at 100k×256M
  (older solver). A deep pass scoped to only the ~49 deferring rows is
  estimated at roughly +45–50 min at `--jobs 8` (the durable rows burn the
  full budget by construction; own-arm walls at 1M ran 120s–2,600s per row in
  the cross-run).

**Arithmetic ceiling of pure budget policy:** +25 agree conversions measured
(19 capacity + 6 over_budget), likely +26 with `tso_minimize[23]`, taking
agree 507 → ~532–533 of 564 with zero engineering risk. The absolute ceiling
if the durable tail also fell: ~552 (564 − 6 typed jar-parity defers − 3
jar-nonverdict rows − fullsub2[0], plus the three nonverdict rows can still
become mettle-answers-where-the-jar-can't).

## Decision (proposed ranking — each option a separate owner call)

**Option 1 — the deep-retry tier (harness only). RECOMMENDED. ~1–2 agent-days,
+25–26 agree, zero lottery risk.** Rows that defer at the standing defaults are
re-run once at a deep tier (1M conflicts × 256M encode — both axes raised,
never lowered, so the elevator[18]-class interaction cannot bite). The standing
defaults and ADR-0017's pairing rule are untouched — this is not a re-pair; it
is a new, documented second tier the ADR never evaluated, and it is symmetric
with how the jar side was banked in the first place (the jar baselines are
themselves a two-tier ladder: the 60s file pass plus the 2700s slow-verdict
tier — a mettle-side ladder compares like with like). Wall: the deep tier
touches only the deferring rows (~+45–50 min when run); under the standing
batched-sweep rule it runs at wrap alongside the stage-1 sweep, and the
known-capped-list discipline applies (results baselined, config-stamped,
hard-error on mismatch). **The genuine fork for the owner is scorecard
framing:** the headline either becomes two numbers ("agree-at-defaults 507 /
agree-with-deep-retry ~532") or stays one number with the tier documented.
Recommendation: the two-number form — it keeps the drop-in-at-defaults claim
honest while banking the measured conversions.

**Option 2 — the `Simplifier`/`inferPartialInstance` probe, then possibly the
build.** The jar's general bound-tightening pass is a confirmed, named,
unimplemented gap (mettle ports only its `util/ordering` special case, mt-035)
and is the only lever that attacks the capacity family at its root — fewer
gates at the *standing* defaults — with **zero trajectory-lottery risk**
(verdict-preserving by the jar's own design). But its scorecard value after
Option 1 is ~0 (the same rows convert either way); what it buys is fidelity
and wall. Cost: a cheap probe first (~1–2 days: does the jar's Simplifier
actually tighten correctChord/TransForm's bounds, or are their hand-declared
scopes already tight?), then 10–15+ days for the faithful pinned build only if
the probe says yes. Recommendation: park unless the owner wants capacity rows
converting at defaults specifically.

**Option 3 — one solver-strength stage: target phases + rephasing, with
stable/focused mode switching, bundled (the CaDiCaL/Kissat pairing).** The
best-evidenced bet left standing on the durable 22: a genuinely untried
*category* (decision-heuristic guidance and restart-regime alternation —
mettle has phase saving but no target phases, no rephasing, no mode switching),
categorically distinct from the three rejected volume/retention mechanisms,
fully determinism-compatible, ~5–8 agent-days. Honest odds: the corpus has
priced three consecutive trajectory perturbations at −2/−2/−6, and nothing in
the record isolates how much of CaDiCaL's 21-of-22 durable-row edge is this
mechanism versus its inprocessing stack — expected value unknown, possibly
negative. If authorized: mt-093 discipline verbatim (one stage,
predictions-first, full row-diff, revert on net-negative). Aged-core tier
retention (the diagnosed fix to stage 3's unaged ratchet, ~2–4 days on the
banked patch) is the natural second stage *only if* this one nets positive.

**Option 4 — accept the durable tail as documented capacity.** After Option 1
the residual is ~23 typed defers, every one individually understood (20
CaDiCaL-answerable search-bound rows, the 3 jar-nonverdict rows, fullsub2[0]),
honestly recorded in LIMITATIONS with `--solver cadical` as the existing
escape hatch. Zero cost. This is the standing state if nothing is authorized.

**Not recommended, with reasons:** chronological backtracking (8–15 days;
ADR-0021's own reconsideration gate — a profile attributing the residual gap
to deep narrow backjumps — was never run and must precede any attempt);
CNF-level BVE/subsumption/BCE (8–12 days, the largest correctness surface in
the survey, colliding with the COUNT_MISMATCH-0 counting contract, and it
cannot touch the capacity family since those rows fail during encoding
itself); reduce/restart parameter tuning (the exact mechanism space measured
dead three times); CaDiCaL as default (owner-decided the other way, ADR-0019).

## Consequences

- Nothing ships from this bead; the tree is untouched. The full per-row fact
  table and the lever survey are banked at `scratchpad/mt119/`.
- If Option 1 is taken, the gauge gains a second tier and the scorecard gains
  a second headline number; the ADR-0017 defaults, the counting nets, and the
  drop-in claim at defaults are all unchanged. Its acceptance gate is
  mechanical: the deep tier's row-diff must show exactly the predicted
  conversions, DISAGREE 0, and byte-stable results everywhere else.
- The sizing surfaced one correction now recorded here: the `capacity` bucket
  had drifted in prose toward "var cap" — it is the encode-op ceiling, and
  LIMITATIONS/STATE language should say so.

## Alternatives considered

Covered above as Options 2–4 and the not-recommended list — this ADR is
itself the alternatives analysis; the decision it proposes is the ranking and
the recommendation to take Option 1 first.

## Addendum (2026-08-24, same day — the option space is reshaped by ADR-0027)

The owner, with this ranking in front of them, reopened the solver-posture
question directly and decided **[ADR-0027](0027-cadical-only-solver.md)**:
CaDiCaL becomes the default solver behind the maintained `Solver` plugin seam,
and the own CDCL is deleted after a gated migration. Effect on this ADR's
options: **Option 3 (own-solver strength stage) is retired outright** — its
premise (improving the hand-rolled solver toward CaDiCaL) is moot; **Option 1
(deep-retry tier) is deferred** until after the migration's mandatory ADR-0017
budget re-pair, then re-derived against whatever tail remains (CaDiCaL's speed
is expected to convert much of the 49 at re-paired defaults); **Option 2
(Simplifier bound-tightening) survives in principle** — encode size is
solver-independent — but is re-priced after the re-pair. The fact base
(Context above, `scratchpad/mt119/`) is unaffected and is part of ADR-0027's
evidentiary record. Status stays Proposed as a record of the ranking; the
live decision now lives in ADR-0027.
