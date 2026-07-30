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

## Addendum — stage-2 decisions (2026-07-30, tech lead)

The decision above stands unchanged, and its text is left as written. These are
the choices stage 2 (the shipped surface) had to make inside it.

1. **Naming: `--solver mettle | cadical`, default `mettle`.** The own solver
   gets the product's own name because it *is* the product's answer — Alloy's
   own surface names backends after the solver (`sat4j`, `minisat`), and
   `--solver cdcl` would have named an algorithm every backend implements. Exact
   match only: no case folding, no prefixes, no aliases, so a recorded command
   means one thing forever. An unresolvable name is a hard usage error (exit 2)
   listing what this build has — the mt-006 no-silent-default rule — and a name
   that exists in the source but was compiled out gets a *different* message
   naming the cargo feature that fixes it, because "typo" and "not built in" are
   different problems with different fixes.

2. **Feature posture: OFF in everything we ship, opt-in from source.** The
   `cadical` feature on the `mettle` crate is off by default, so the release
   artifacts, the container image and the nix package remain the all-Rust,
   zero-C-toolchain builds ADR-0016 designed. This ADR contemplated shipping it
   enabled "if the release matrix + flake can build the C++ dep on all four
   targets" — and that condition is **not yet demonstrated**. Verified locally
   (host `aarch64-apple-darwin` only): the feature builds in release, the
   `--solver cadical` surface works end to end, and the C++ compiles from the
   vendored sources with no system library. Not verified, and therefore not
   claimed: the other three targets, the `rust:1.97.0-slim` Docker builder
   (needs `g++`, and `distroless/cc` may not carry `libstdc++`), and the
   sandboxed nix build (needs a C++ compiler in `nativeBuildInputs`). The
   evidence to flip this is now collected automatically:
   `.github/workflows/backend-determinism.yml` builds the feature on all four
   release runners and fails if any cannot, on every `v*` tag. Flipping the
   default is a follow-up bead once that has actually run — not a claim made in
   advance of its own experiment.

3. **Budget mapping: `--conflicts` binds, spend is unobservable.** CaDiCaL's
   `limit("conflicts", n)` is per-solve-relative (`lim.conflicts =
   stats.conflicts + inc.conflicts` at each solve's start), which is exactly the
   own solver's `solve_within` contract, so the flag means the same thing on both
   and needs no reinterpretation. `u64::MAX` (no budget) is passed as CaDiCaL's
   own unlimited sentinel `-1` rather than saturating to `i32::MAX`, so a caller
   who asked for no budget can never be told "budget exhausted". What has no
   analogue is the *counter*: nothing in the crate, its C shim, or the vendored
   C++ exposes conflicts/decisions/propagations as a value (`Stats` is private to
   `Internal`; the C API's only statistics call prints). So
   `LiveSolver::effort()` is `Option`, the cumulative enumeration-effort budget
   is **refused** on an effort-less backend instead of being charged zero, and the
   gap is disclosed in `--help` and LIMITATIONS.

4. **Enumeration works; counting stays own-CDCL.** Enumeration under CaDiCaL is
   exact by the same argument it is exact under the own solver (a sound solver
   plus the same blocking clauses over the same primary variables), so `serve`'s
   "next" and the trace enumerator work under `--solver cadical` — with the order,
   the first instance, and a temporal command's locked configuration all being
   the backend's own (LEDGER-014). Counting is fenced structurally rather than by
   convention: the conformance gauge has **no** `--solver` flag, so no baseline
   or scorecard number can be produced on anything but the yardstick.

5. **The cross-backend arm lives in the instrument, not the gauge.**
   `backend-instrument --cross` (dev-side, `cadical-instrument` feature) encodes
   each worklist row **once** and decides that one CNF with both backends,
   exiting non-zero on any verdict difference or self-check failure. Translating
   once is the point: "same bounds, same numbering, same SBP, same budget" is then
   true by construction rather than by re-derivation. Putting it here rather than
   in `solve-gauge` keeps the scorecard instrument single-backend by construction
   (decision 4) while giving the check a home that already has worklists,
   parallelism and per-row artifacts.

6. **FP discipline lives in the build definition, so every build shares it.** `.cargo/config.toml` sets
   `CXXFLAGS=-ffp-contract=off` (not forced, so a packager's own flags win),
   which the `cc` crate appends to every C++ compile. The crate's `build.rs`
   pins only `-O3 -DNDEBUG -std=c++17`, and CaDiCaL's restart policy compares
   `double` EMAs, so FMA contraction was a live cross-architecture divergence
   licence; this withdraws it. No `-ffast-math` anywhere. This does not *make*
   the backend cross-platform byte-identical — it removes the one cause we can
   name, and the battery measures what is left.
