# ADR-0019 — An optional CaDiCaL SAT backend behind the `Solver` trait; the own CDCL stays the yardstick

**Status:** Accepted (owner-decided, 2026-07-29)
**Date:** 2026-07-29
**Revises:** [ADR-0011](0011-rung3-translation-solving-architecture.md)'s single-backend posture (the own-solver decision itself stands — it remains the default and the conformance yardstick).

## Context

ADR-0011 chose a hand-rolled, zero-dependency, deterministic-by-construction
CDCL so that verdicts, instances, and enumeration counts are byte-identical
per build and fully under our control — the foundation the counting nets and
the temporal-enumeration semantics (LEDGER-014) are pinned on. The cost,
measured across the conversion campaign, is search power: the solver is
deliberately minimal (integer VSIDS, Luby restarts, 1-UIP, keep-all clause
database), and the remaining `over_budget` tail (47 rows at the mt-087
100k×64M defaults) sits exactly in the regime where modern solvers with
clause-database management, phase saving, and inprocessing dominate. The
reference jar is itself multi-backend (`A4Options` solver choice; the dist
default SAT4J is a mature MiniSat-lineage solver), so a solver-choice surface
is Alloy-shaped, not foreign to it.

## Decision

1. **mettle gains an optional second SAT backend — CaDiCaL** (MIT-licensed,
   state-of-the-art, incremental via IPASIR, conflict-limit capable) —
   integrated behind the existing `als_solve::Solver` trait. The owner
   explicitly accepts that the alternative backend is **not held to the
   byte-identical determinism contract**: it is "legit and way more powerful,"
   and that trade is the point.
2. **The own CDCL remains the default** for every command, and remains the
   **only** backend the conformance scorecard, the counting nets, and the
   sweep baselines are measured on. The determinism contract (fixed build ⇒
   byte-identical output) continues to bind the default path unchanged.
3. **Instrument first, surface second** (bead mt-089, staged): the backend is
   first wired dev-side and run over the defer tail to measure, per row,
   "genuinely hard" vs "our solver is weak" — the complement to the mt-088
   budget census, and the prioritizer for family-D solver work. Only then is
   the user surface (`--solver`) shipped.
4. **Honesty requirements for the shipped surface:** the alternative backend
   is documented in LIMITATIONS as deterministic-per-build but not
   cross-platform byte-pinned; temporal *counts* under it are
   configuration-relative to *its* first solution (LEDGER-014) and are not
   compared against jar baselines; verdicts, however, are backend-independent
   truths — any verdict difference between backends on the same encoding is a
   bug, and the gauge gains a cross-backend arm to exploit exactly that as a
   free oracle-independent check.

## Consequences

- A written dependency justification (project principle) for the chosen
  binding path — an existing binding crate or vendored C++ built via `cc` —
  including its effect on the four cargo-dist targets and the nix flake.
  CaDiCaL (not Kissat) because enumeration needs incremental solving.
- The `Solver` trait seam (already dependency-free by ADR-0005/mt-032) is the
  integration boundary; the enumeration path's `add_clause`/`block` semantics
  must be preserved through IPASIR's incremental interface.
- The scorecard's meaning does not move: 100% drop-in is still measured on
  the default backend at the ADR-0017 defaults.
- Family-D solver upgrades to the own CDCL remain on the roadmap; the
  instrument stage tells us which upgrades pay before we build them.

## Alternatives considered

- **Pure-Rust backends (`splr`, `varisat`, `batsat`)** — keep the all-Rust
  static build, but are MiniSat-class at best: they would blunt the
  instrument's main question (how much of the tail is solver-weakness) by
  measuring with a middling solver. Rejected for the instrument; not excluded
  as a future third option if packaging friction with C++ proves high.
- **Making CaDiCaL the default** — rejected: it would move correctness-
  critical, contract-pinned behavior (determinism, enumeration, temporal
  config-locking) into code we don't own, and decouple the scorecard from the
  binary most users run.
- **Family-D upgrades only, no second backend** — rejected as the sole path:
  without a strong-solver instrument we cannot tell which tail rows any
  amount of textbook upgrading can reach, and the owner values offering users
  the powerful option directly.
