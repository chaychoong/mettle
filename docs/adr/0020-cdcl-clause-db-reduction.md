# ADR-0020 — Family-D stage 1: attribute the own CDCL's measured wall gap, then fix the first-order term

**Status:** Accepted (tech-lead decision, 2026-07-30; revised same day, pre-implementation — see the revision note)
**Date:** 2026-07-30
**Builds on:** [ADR-0019](0019-optional-cadical-backend.md) (the instrument whose measurements this decision consumes), [ADR-0017](0017-gauge-default-budgets-paired-frontier.md) (the pairing rule this change triggers), [ADR-0011](0011-rung3-translation-solving-architecture.md) (the own-solver architecture, unchanged).

## Revision note (2026-07-30, same day, before any implementation)

The first version of this ADR (commit `410fd08`) inherited a context error
from ADR-0019 and prescribed **clause-database reduction** as the fix. The
code says otherwise, checked before delegating the work:

- The own CDCL has had **deterministic LBD-based clause-DB reduction since
  mt-049** (`als-solve/src/solver.rs` module docs and `reduce_db`: conflict-count
  schedule `REDUCE_FIRST_DEFAULT = 2_000` / `+300`, integer-LBD ranking with a
  lowest-index tie-break, delete-half by tombstone, locked/permanent clauses
  exempt — roughly 20 reductions fire inside a 100k-conflict run). It also has
  **phase saving** and **Luby restarts**. ADR-0019's "keep-all clause database"
  context line was wrong.
- The "measured implication order" recorded at the mt-089 session wrap
  ("clause-DB reduction first, then phase saving, restart policy…") appears
  **nowhere in the mt-089 artifacts** (`scratchpad/probe/mt089/NOTES.md` has no
  such attribution) and is contradicted by the code. **Retracted.** What the
  instrument measured is the **gap** (40.6× wall on ertms_1A[9] on the identical
  CNF); it never measured the gap's **attribution** to a solver component.

The economic case below (which rows convert, at what budget, and the re-pair
mechanism that turns cheaper conflicts into agreements) is unchanged — it
depends on the size of the wall gap, not on which component causes it. The
decision is reshaped to match what is actually known: **profile first, then
fix the measured term.**

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
elevator_spl_events[0], 48.9× on handshake[0].

**What the own CDCL actually is** (solver.rs, verified 2026-07-30): integer
VSIDS with phase saving, 1-UIP learning, Luby restarts, and mt-049's
deterministic LBD reduction. **Unmeasured suspects for the wall gap, in the
tech lead's prior order:**

1. **`pick_branch` is a linear scan over the whole dense variable pool on
   every decision** — O(vars) per decision, documented in-file as "ample for
   Rung-3 scope". On the pathological rows (10⁵–10⁶ variables, 10⁵–10⁶
   decisions) that is a quadratic-order total cost no modern solver pays
   (they use a heap / order structure).
2. **No learned-clause minimization** (recursive or basic) — longer learned
   clauses cost propagation forever after.
3. **Watch-scheme quality** — no blocking literals; every watch visit touches
   the clause arena.
4. `reduce_db` ranking/schedule quality and restart-policy details — present
   but simpler than CaDiCaL's.

All four have determinism-compatible fixes (integer activities with total
tie-orders give a deterministic heap; minimization is a pure function of the
implication graph; blocking literals are cache engineering).

Why a wall-side fix converts rows when the budget is denominated in conflicts:
the defaults sit on the ADR-0017 **wall-cost** frontier. Whatever makes late
conflicts expensive prices 250k conflicts at 2.2× and 1M at 8.1× of the
default wall; cheaper conflicts move the frontier, and the standing pairing
rule re-pairs the default upward at the same absolute wall. This mechanism ran
once already: mt-087's gate cache cut per-conflict cost ~2× and the default
moved 25k → 100k with zero regressions. mt-088's decision to HOLD the defaults
anticipated this ADR ("any family-D solver work moves the frontier again").

## Decision

**Proceed — bead mt-092, two stages, gate between them.**

**Stage 0 (attribution profile, mt-080-style, predictions written first):**
deterministically instrument the own CDCL on the calibration outliers
(ertms_1A[9] 560.6s, elevator_spl_events[0] 14.6s, handshake[0] 6.3s — jar
agreement already banked for all three) and attribute wall time across:
decision picking, propagation (watch visits, clause-arena touches),
conflict analysis + minimization opportunity (learned-clause lengths), and
`reduce_db` (DB size over time, deletion effectiveness). The profile names
the first-order term; the instrument stays dev-side and off the default path.

**Stage 1 (the fix):** implement the measured first-order term's fix under the
constraints below. If stage 0 attributes the gap to something whose fix would
break a standing contract, the decision comes back to this ADR before code.

**Yield estimate (stated before implementation, scored at the grid).** Base
case **+13 agreements at re-paired defaults**: the G1 band converts if the fix
buys ~2× wall on the long rows, bringing the 250k point from 1,556s into the
~700s envelope the ADR-0017 knee accepts. Upside **+23** (the 1M band needs
~8×; the measured 40× per-row gap says that much is available on *some* rows,
and it is not assumed for all). The durable-23 tail is explicitly **not** the
target: rows where CaDiCaL needs ≤100k conflicts while the own CDCL needs >1M
are separated by search quality, which wall-side fixes alone do not close.
Secondary payoff, real either way: every future sweep, grid, and battery gets
cheaper — measurement wall is now a first-order line item (G2 5,666s; the
three-net battery ~37 min).

The 20 `capacity` rows are encode-bound (G3: all 20 fit under a 256M encode
budget, 19 agree at once) and are untouched by this decision; the encode axis
re-enters at the next paired grid on its own merits.

## Constraints (binding on mt-092, whatever the fix turns out to be)

1. **Determinism by construction.** Any new decision/ranking structure keeps a
   total deterministic order (integer activities, lowest-index tie-break — no
   wall-clock, no allocation addresses, no float ties). The run-to-run
   byte-identity tests keep their teeth, and the 4-target
   `backend-determinism.yml` battery treats an own-CDCL hash split as CI
   failure.
2. **The counting contract stays exact.** Blocking clauses (enumeration) and
   locked-configuration units (temporal, LEDGER-014) stay permanent; reason
   clauses stay locked while referenced (both already the mt-049 rule).
   Acceptance: **COUNT_MISMATCH 0 at SB-0 and SB-20**; rows moving between
   `count_match` and typed `enum_budget` skips are disclosed, mismatches are
   stop-the-line.
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
   affordable post-fix).
6. **Instance re-pins are expected and disclosed.** A changed search
   trajectory may change first instances on SAT rows; goldens that pin
   specific instances re-capture with the change disclosed. The determinism
   contract is fixed-build byte-identity (ADR-0011), and enumeration order is
   the backend's own (LEDGER-014) — neither promises instance stability
   across solver versions.

## Consequences

- Stage 0 validates the whole bead's premise on the pathological rows before
  any solver code changes — the owner's standing
  validate-on-the-pathological-case rule, and this ADR's own revision history
  is the argument for it.
- The gate for stage 1: full gauntlet green; fresh stage-1 sweep row-diffed
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
conflicts, and the instrument measured a 9–49× per-row wall gap to a
state-of-the-art solver on identical CNFs. Parking now would freeze a
proven-convertible mass out of the scorecard while holding a measured,
determinism-compatible lever. Parking remains the recorded fallback if
mt-092's grid disappoints.

**Skip the profile and fix the strongest suspect (the linear decision scan)
directly.** Rejected: the measure-first discipline exists because the last two
attribution guesses were wrong in opposite directions — mt-086's hash-consing
forecast over-promised (0 of 28 rows), and this ADR's own first version
prescribed a component that already exists. A three-row profile costs about an
hour and makes stage 1 attributable.

**Jump straight to the full upgrade ladder (heap + minimization + watch
engineering + reduce tuning) in one bead.** Rejected: the techniques compose
but are separately testable, and a single-technique stage keeps the re-pair
grid attributable — if the frontier moves, we know what moved it (the same
discipline that made mt-086/mt-087 legible).

**Adopt CaDiCaL as the default instead of improving the own CDCL.** Already
decided the other way by the owner in ADR-0019: the own CDCL stays the default
and the yardstick precisely because its determinism contract underpins the
counting nets and baselines. This ADR is the complement ADR-0019 §3 promised —
the instrument prioritizing family-D work on the own solver.
