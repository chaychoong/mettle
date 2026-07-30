# ADR-0020 — Family-D stage 1: deterministic clause-database reduction in the own CDCL

**Status:** Accepted (tech-lead decision, 2026-07-30)
**Date:** 2026-07-30
**Builds on:** [ADR-0019](0019-optional-cadical-backend.md) (the instrument whose measurements this decision consumes), [ADR-0017](0017-gauge-default-budgets-paired-frontier.md) (the pairing rule this change triggers), [ADR-0011](0011-rung3-translation-solving-architecture.md) (the own-solver architecture, unchanged).

## Context

At the 100k-conflict × 64M-encode defaults the scorecard is agree 484 with 47
`over_budget` + 20 `capacity` typed defers. The mt-088 census priced the 47
exactly (per-row bands verified against `scratchpad/mt087grid/rebase-stage1.json`
and `scratchpad/mt088census/G1/G2`):

- **13 rows convert at 250k conflicts** (G1; sweep wall 1,556s vs 701s at
  defaults — 2.2×): elevator_spl_events ×6, both handshake[1]s, hotel4[0],
  firewire[4], textbookSnapshotIsolation[0], lc-lenses[7], hanoi[0].
- **11 more at 1M** (G2; 5,666s — 8.1×): 10 agreements (ertms_1A ×3,
  lc-lenses ×3, elevator ×2, distribution[0], buffer[2]) plus
  correctChord[13] answering a row the jar's own 2700s banking could not.
- **23 rows are durable at 1M** — the tail mt-089 instrumented.

The mt-089 instrument separated solver weakness from genuine hardness on that
tail: CaDiCaL converts 21 of 23 (only 7 within 100k conflicts; 14 more need
1M), and the 11-row calibration measured the own CDCL's wall gap on the same
CNF — **40.6× on ertms_1A[9]** (560.6s / 380,956 conflicts vs 13.8s), 9.3× on
elevator_spl_events[0], 48.9× on handshake[0]. The own CDCL is deliberately
minimal: integer VSIDS, Luby restarts, 1-UIP learning, and a **keep-all clause
database**. The measured implication order for closing the gap (mt-089 stage 1,
recorded in TASKS): **clause-DB reduction first**; phase saving and restart
policy after; inprocessing not implicated; BCP micro-opts least.

Why reduction converts rows when the budget is denominated in conflicts, not
seconds: the defaults sit on the ADR-0017 **wall-cost** frontier. A keep-all
database makes late conflicts expensive — BCP walks every learned clause for
the rest of the run — and that cost curve is what prices 250k conflicts at
2.2× and 1M at 8.1× of the default wall. Cheaper conflicts move the frontier,
and the standing pairing rule then re-pairs the default upward at the same
absolute wall. This exact mechanism ran once already: mt-087's gate cache cut
per-conflict cost ~2× and the default moved 25k → 100k with zero regressions.
mt-088's decision to HOLD the defaults anticipated this ADR ("any family-D
solver work moves the frontier again").

## Decision

**Proceed — bead mt-092: implement deterministic clause-database reduction in
the own CDCL.** Scope is reduction only. Phase saving and restart policy are
separate future beads, filed only if a post-reduction re-run of the instrument
still implicates them.

**Yield estimate (stated before implementation, mt-089-style).** Base case
**+13 agreements at re-paired defaults**: the G1 band converts if reduction
buys ~2× wall on the long rows, bringing the 250k point from 1,556s into the
~700s envelope the ADR-0017 knee accepts. Upside **+23** (the 1M band needs
~8×; the measured 40× per-row gap says that much is available on *some* rows,
and it is not assumed for all). The durable-23 tail is explicitly **not** the
target: rows where CaDiCaL needs ≤100k conflicts while the own CDCL needs >1M
are separated by search quality (clause usefulness, phase saving, restarts),
which deletion alone does not close. Secondary payoff, real either way: every
future sweep, grid, and battery gets cheaper — measurement wall is now a
first-order line item (G2 5,666s; the three-net battery ~37 min).

The 20 `capacity` rows are encode-bound (G3: all 20 fit under a 256M encode
budget, 19 agree at once) and are untouched by this decision; the encode axis
re-enters at the next paired grid on its own merits.

## Constraints (binding on mt-092)

1. **Determinism by construction.** Reduction triggers on a conflict-count
   schedule; victim selection uses a total deterministic order (glue/LBD, then
   size, then clause id — no wall-clock, no allocation addresses, no float
   activity ties). The run-to-run byte-identity tests keep their teeth, and
   the 4-target `backend-determinism.yml` battery treats an own-CDCL hash
   split as CI failure.
2. **The counting contract stays exact.** Blocking clauses (enumeration) and
   locked-configuration units (temporal, LEDGER-014) are irredundant — never
   candidates for deletion; clauses that are the reason of a trail literal are
   locked while referenced. Acceptance: **COUNT_MISMATCH 0 at SB-0 and SB-20**;
   rows moving between `count_match` and typed `enum_budget` skips are
   disclosed, mismatches are stop-the-line.
3. **Effort semantics unchanged.** `effort()` keeps meaning conflicts; the
   enumeration-effort budget keeps its cumulative meaning.
4. **The pairing rule fires.** A full ADR-0017 paired-grid re-pair is
   mandatory after landing; the mt-088 census JSONs are the banked comparison
   points. Regressions at the chosen default must be zero or individually
   disclosed-and-decided (ADR-0018's recoverable-loss precedent).
5. **Wrong-verdict insurance.** The acceptance battery includes
   `backend-instrument --cross` on the defer tail with the own arm at 1M+
   conflicts and the CaDiCaL arm as the check — the exact configuration that
   caught mt-090 — plus DISAGREE 0 on every sweep. This doubles as the deep
   tail cross-run mt-089 disclosed as pending (the own arm's 1M+ wall becomes
   affordable post-reduction).
6. **Instance re-pins are expected and disclosed.** Deletion changes the
   search trajectory, so first instances on SAT rows may change; goldens that
   pin specific instances re-capture with the change disclosed. The
   determinism contract is fixed-build byte-identity (ADR-0011), and
   enumeration order is the backend's own (LEDGER-014) — neither promises
   instance stability across solver versions.

## Consequences

- mt-092 validates on the pathological calibration rows first (ertms_1A[9],
  elevator_spl_events[0]) before any sweep — the owner's standing
  validate-on-the-pathological-case rule.
- The gate for the bead: full gauntlet green; fresh stage-1 sweep row-diffed
  (defer→agree moves and disclosed re-pins only); the paired grid run and a
  new default chosen (or the incumbent confirmed) per ADR-0017; both count
  nets mismatch-free; the cross-backend tail run split-free; the determinism
  battery unchanged on the own arm.
- If the measured yield lands under the base case (+13 fails to materialize
  at an acceptable wall), the fallback is the rejected alternative below:
  park with the tail disclosed. The grid decides; the estimate above is the
  prediction it is scored against.

## Alternatives considered

**Park the conversion campaign at 484.** Rejected: the census proved 24 of the
47 over_budget rows convert on budget alone — the barrier is the wall cost of
conflicts, and the instrument measured keep-all clause storage as the
first-order term in exactly that cost. Parking now would freeze a
proven-convertible mass out of the scorecard while holding a measured,
well-understood, determinism-compatible lever. Parking remains the recorded
fallback if mt-092's grid disappoints.

**Jump straight to the full upgrade ladder (reduction + phase saving +
restarts) in one bead.** Rejected: the implication order is measured, the
techniques compose but are separately testable, and a single-technique bead
keeps the re-pair grid attributable — if the frontier moves, we know what
moved it (the same discipline that made mt-086/mt-087 legible).

**Adopt CaDiCaL as the default instead of improving the own CDCL.** Already
decided the other way by the owner in ADR-0019: the own CDCL stays the default
and the yardstick precisely because its determinism contract underpins the
counting nets and baselines. This ADR is the complement ADR-0019 §3 promised —
the instrument prioritizing family-D work on the own solver.
