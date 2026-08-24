# vendor/ — third-party source mettle carries in-tree

One entry today: `cadical/`, a lightly patched copy of the `cadical` crate.

## Provenance

| | |
|---|---|
| crate | [`cadical` 0.1.16](https://crates.io/crates/cadical) (crates.io), by Miklos Maroti — MIT |
| bundled solver | CaDiCaL 1.9.5, by Armin Biere et al. (`cadical/`, `cadical/VERSION`) — MIT |
| pristine source | the registry checkout under `~/.cargo/registry/src/*/cadical-0.1.16` |
| local delta | `vendor/cadical-mettle.patch` — 4 files, 124 added lines, 1 changed |

Both licenses ship as they came: `cadical/LICENSE` (the solver) and `LICENSE`
(the binding). The root `NOTICE` names them for anyone redistributing a mettle
binary, which now statically links both.

The registry copy is taken as-is except for three files cargo keeps for its own
bookkeeping and a path dependency never reads: `.cargo-ok`, `Cargo.lock`, and
`Cargo.toml.orig`.

## Why a fork exists

mettle needs two things from CaDiCaL that the published binding cannot express,
both load-bearing rather than nice to have
([ADR-0027](../docs/adr/0027-cadical-only-solver.md), proven out by the mt-120
spike):

1. **Search-effort counters.** The cumulative enumeration budget
   (`SolveOptions::enum_effort_budget`) is charged from what the solver spent,
   so a backend with no counters cannot be enumerated under a budget at all —
   the mt-120 spike measured exactly that failure. CaDiCaL keeps the numbers in
   `Internal::stats`, which is private to the solver; the public `Solver` had no
   accessor, `ccadical.h` has none, and `ccadical_print_statistics` only prints
   (into a build that also defines `-DQUIET`). ADR-0019 recorded the resulting
   "budgets bind, spend is unobservable" gap; this patch closes it.
2. **Proof tracing.** ADR-0027 decision 4 certifies UNSAT verdicts with
   DRAT/LRAT proofs. CaDiCaL has had the machinery all along (`-DNTRACING`
   disables *API-call* tracing, not proof tracing) and its C API even exposes
   `ccadical_trace_proof` — but that entry point hands the caller a `FILE *`,
   and the Rust binding wraps none of it.

Neither can be reached from outside the crate, so the fork is permanent, not a
migration artifact. It is kept as small as a fork can be: three read-only C++
accessors, five C entry points, six safe Rust wrappers, and one null-pointer
guard. **The search is untouched** — no heuristic, no data structure, and no
compile flag differs from the published crate, which is what lets the mt-120
bit-reproducibility evidence carry over.

## What the patch adds

| file | change |
|---|---|
| `cadical/src/cadical.hpp` | declares `Solver::conflicts/decisions/propagations` |
| `cadical/src/solver.cpp` | defines them off `internal->stats` (`propagations` is the **search** sub-counter only — the inprocessing terms measure simplification, not the CDCL search a conflict budget prices), and stops `trace_proof(path)` connecting a tracer to a file it failed to open |
| `src/ccadical.cpp` | `ccadical_conflicts/_decisions/_propagations`, plus `ccadical_trace_proof_path` (the path-only tracer entry point; the upstream C name is already taken by the `FILE *` form) and `ccadical_flush_proof` |
| `src/lib.rs` | extern declarations and safe `Solver` methods for all of the above, plus `close_proof_trace` over upstream's existing `ccadical_close_proof` |

The `trace_proof` guard is a genuine upstream bug: on a path it cannot open,
CaDiCaL builds a `DratTracer` over a null `File` and segfaults on the first
proof line — the very failure the function's `bool` return exists to report.
With the guard, an unopenable path is a `false` and nothing else happens.

Two contracts the C++ enforces by aborting the process, so mettle's
`CadicalSolver` keeps callers away from them:

- `trace_proof` is only legal in the CONFIGURING state — **before the first
  clause and before the variable reservation**, both of which leave it;
- `flush_proof_trace` / `close_proof_trace` are only legal while a trace is
  open, and closing twice aborts.

## Regenerating

```sh
./scripts/vendor-cadical.sh
```

Copies the registry checkout, strips the three bookkeeping files, and applies
`cadical-mettle.patch`. It is idempotent: a clean tree in, the same tree out. If
regenerating leaves `vendor/cadical` dirty, the patch and the vendored copy have
drifted — re-derive the patch from the two trees rather than editing both by
hand (the header of the script says how).

`vendor/cadical` is deliberately **not** a workspace member (`exclude` in the
root `Cargo.toml`). It is upstream code: the workspace's `unsafe_code = "forbid"`
would reject an FFI binding outright, and its formatting and clippy posture are
the binding author's business, not ours.
