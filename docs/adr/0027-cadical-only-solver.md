# ADR-0027 — CaDiCaL becomes the default solver behind a maintained plugin seam; the own CDCL is deleted after migration; verdicts are certified by self-check + proof logging

**Status:** Accepted (owner-decided, 2026-08-24) — migration gated on the §3 spike; supersedes the shipped-posture half of [ADR-0019](0019-optional-cadical-backend.md)
**Date:** 2026-08-24
**Supersedes:** [ADR-0019](0019-optional-cadical-backend.md)'s posture decision ("own CDCL stays default + yardstick"); ADR-0019's integration record (the `Solver` trait boundary, the backend mapping, the instrument) remains accurate and is built on here. Also reshapes [ADR-0026](0026-compute-tail-sized-plan.md)'s option space (addendum there).

## Context

Three facts accumulated against the own-solver posture since ADR-0019:

1. **The solver-strength campaign closed 0-for-3** ([ADR-0021](0021-cdcl-volume-lever.md)): trail saving, all-UIP shrinking, and tier retention were each implemented well, measured honestly, and rejected by the corpus (−2/−2/−6). The standing lesson: this corpus prices trajectory perturbations at zero to negative.
2. **The tail is proven answerable by CaDiCaL, on our own CNFs**: the mt-092 closing cross-run answered 21 of the 22 durable `over_budget` rows within a 900s wall at the same conflict-budget configuration. The gap is search quality in the hand-rolled solver, not the encoding.
3. **The mt-119 sizing ([ADR-0026](0026-compute-tail-sized-plan.md))** priced the best remaining own-solver idea (target phases + rephasing + mode switching) at 5–8 agent-days with odds honestly unknown — a bet to *approach* what CaDiCaL already does.

The owner then asked the direct question this ADR answers: is there any point
keeping the own solver at all? The examination (recorded in the 2026-08-24
session; sizing fact base at `scratchpad/mt119/`) found that every load-bearing
role the own solver plays can be carried without it:

- **Enumeration** is solve → block → incremental re-solve; CaDiCaL's IPASIR
  seam supports it, and the shipped backend already maps `add_clause`
  incrementally and binds conflict budgets via `ccadical_limit("conflicts", n)`
  (`als-solve/src/cadical_backend.rs`).
- **Counting** (the SB-0/SB-20 nets) is solver-independent by construction:
  the totals are "how many models exist over the primary variables", a
  property of the CNF plus exhaustive blocking, not of the search trajectory.
  Parity is re-verifiable against the cached jar count baselines with the
  existing instruments.
- **The cross-audit** existed to check the risky hand-rolled component; the
  component's deletion removes the audit's subject. Its replacement is
  *stronger*: SAT verdicts are already certified by the evaluator self-check
  (solver-independent, stays), and UNSAT verdicts become certifiable by
  CaDiCaL's native DRAT/LRAT proof logging — a machine-checkable certificate
  where the cross-run only ever offered "two solvers agreed". (Two solvers
  agreeing never audited the encoding anyway — the jar oracle and the
  self-check do that, and both stay.)
- **The precedent is Alloy itself**: the reference has never had its own
  solver — it bundles SAT4J and optional native MiniSat/Glucose behind a
  plugin seam. mettle's `Solver` trait is that seam and stays, so any future
  second opinion (Kissat, MiniSat) is an afternoon's instrument, not
  architecture.

What genuinely changes character is **determinism**: today it is determinism
*by construction* (integer-only arithmetic we wrote); on CaDiCaL it becomes
determinism *by pinning* (an exact vendored version built with pinned flags —
CaDiCaL's activity scores use floating point, so toolchain behavior matters in
theory). The mitigation is a standing **determinism gate**: byte-compared
repeated runs, cross-architecture comparison (aarch64 native vs x86_64, via
Rosetta locally and the release battery's target matrix), run as part of
verification. If pinning cannot deliver bit-reproducibility, this ADR's
migration does not proceed (§3).

## Decision

1. **CaDiCaL becomes the default production solver** — verdicts, instance
   enumeration, temporal trace enumeration, and both counting nets — across
   `exec`, `serve`, the REPL, and the conformance gauge. The `cadical` cargo
   feature stops being optional and becomes part of the default build.
2. **The solver stays swappable — the `Solver` trait is a first-class,
   maintained plugin boundary, not a leftover** (owner requirement, stated
   with this decision; the precedent is Alloy's own solver-plugin seam). The
   migration hardens the trait into a documented backend contract — what any
   backend must provide: incremental `add_clause` across solves (the
   enumeration seam), conflict-budgeted `solve_within` with observable spend,
   model access over the primary variables, and (optionally) proof emission —
   with the gauge/exec drivers written against the trait only, never against
   a concrete backend. `--solver <name>` remains the user surface; future
   backends (Kissat, MiniSat, …) are feature-gated plugins that implement the
   trait and register a name. Anything a backend cannot provide (e.g. a proof
   tracer) degrades to a typed capability refusal, never a silent behavior
   change — the ADR-0019 `effort()`-refusal precedent generalized.
3. **The own `CdclSolver` is deleted after the migration completes** (git
   history keeps it recoverable). The mt-092/093 A/B scaffolding in the
   scratchpad is unaffected (already git-ignored history).
4. **Verdict certification replaces the cross-solver audit:** the evaluator
   self-check certifies SAT (unchanged); DRAT/LRAT proof logging, wired into
   the gauge's audit modes, certifies UNSAT. Proof checking is a gauge/CI
   instrument, not a per-solve default.
5. **The budget contract survives:** `effort()` keeps meaning conflicts.
   Conflict *limits* already bind on the backend; the missing conflict
   *counter* (the binding exposes none — ADR-0019's recorded contract gap)
   is closed during the spike/migration, by FFI extension or by replacing the
   binding crate with direct FFI against the vendored source.
6. **The ADR-0017 pairing rule fires**: a solver change requires a full
   paired-grid re-pair of the default budgets. Expected effect: CaDiCaL's
   speed moves the frontier substantially — much of the 49-row deferred tail
   ([ADR-0026](0026-compute-tail-sized-plan.md)) is expected to convert at
   re-paired defaults before any deep-retry tier is considered.

## 3. The gate: the spike (runs first; migration is conditional on it)

A 2–3 day spike converts the two real unknowns into measured facts before any
migration work starts. **All three criteria must pass:**

1. **Bit-reproducibility.** The full 564-row stage-1 sweep on the CaDiCaL
   backend, run twice → byte-identical reports; and cross-architecture
   (aarch64-darwin native vs x86_64 under Rosetta, same pinned source and
   flags) → byte-identical. Conflict-limited runs must also be reproducible
   (the limit fires at the identical point every run).
2. **Count parity.** SB-0 and SB-20 counting nets enumerated by CaDiCaL →
   COUNT_MISMATCH 0 against the cached jar baselines, and `skip_*` taxonomy
   coherent.
3. **Budget observability.** A conflict counter is obtainable (FFI extension
   or direct binding) so typed `over_budget` defers keep their meaning.

Spike bonus data (non-gating): the 49-row deferred tail measured on CaDiCaL at
the standing budgets — a preview of the re-pair's yield, including the first
CaDiCaL data on the 20 encode-bound capacity rows.

**If the spike fails** on reproducibility or count parity, the migration stops
and the fallback is ADR-0026's option space as filed (deep-retry tier on the
own solver first, hybrid posture reconsidered) with the failure documented
here as an addendum.

## Consequences

- **ADR-0026 is reshaped** (addendum filed there): option 3 (own-solver
  strength stage) is retired outright; option 1 (deep-retry tier) is deferred
  until after the migration's ADR-0017 re-pair, then re-derived against
  whatever tail remains; option 2 (Simplifier bound-tightening) is unaffected
  in principle but re-priced after the re-pair.
- **Instance-shape goldens re-pin.** Which model comes back first changes with
  the solver; exec/XML/REPL/serve tests pinned to instance identity get
  re-pinned once, disclosed as churn (Alloy makes no first-instance guarantee,
  so no conformance meaning attaches).
- **Packaging**: the cross-target CI battery for the vendored C++ (the
  deferred v0.1.2 item, ADR-0016/0019) becomes a migration prerequisite
  instead of an option — shipped builds carry CaDiCaL, so every release
  target must prove it.
- **Dev environments** need a C++ toolchain unconditionally (the nix flake and
  CI already carry one for the feature flag).
- The determinism gate becomes part of the standing verification battery
  (byte-compare double-run at wraps; cross-arch at release tags).
- LIMITATIONS, STATE, and the CLI docs update at migration time (`--solver`
  surface simplifies; the "shipped builds keep cadical off" caveat dies).

## Alternatives considered

**Keep the own solver and keep strengthening it** (ADR-0026 option 3).
Rejected by the owner with the 0-for-3 record and the 21-of-22 cross-run in
front of them: the best case of a 5–8 day uncertain bet is approaching what
the mature solver already delivers.

**Hybrid: CaDiCaL for verdicts, own solver for counting/self-check.**
Considered as the low-rework middle (it was the tech lead's initial
recommendation); rejected for permanent two-engine complexity ("which engine
answered this?") once the examination showed counting ports cleanly and the
audit role is better served by proofs.

**Second external solver as the audit arm** (Kissat/MiniSat). Weaker than
proof certification (agreement is not a certificate), and the trait seam keeps
it available as a future one-off instrument anyway.

**Status quo (ADR-0019).** Its own rationale — determinism underpinning the
counting nets — is preserved by this ADR's gate rather than by the hand-rolled
implementation: the spike must prove pinned-build reproducibility and count
parity before anything ships.
