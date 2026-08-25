# Contributing to mettle

Thanks for looking under the hood. Two kinds of contribution matter most, in this order:

1. **Divergence reports.** You found a model where mettle and the reference Alloy Analyzer disagree. None of the setup below is needed for this. See ["Found a difference from Alloy?"](README.md#found-a-difference-from-alloy) in the README and file an issue.
2. **Code and docs.** The rest of this file.

## Workspace setup

**We use nix.** One command, with nothing else to install or configure:

```sh
nix develop      # exact rustc 1.97.0 + JDK 21 + every tool the scripts use
```

**No nix?** The prerequisites are short, so bring your own:

- **Rust.** [rustup](https://rustup.rs) picks up the toolchain version recorded in `rust-toolchain.toml` automatically, with nothing to configure.
- **JDK 21.** Only needed to run the jar-backed conformance tooling. A plain build and test does not need it.
- `git`, `curl`, `python3`, for the asset-fetch script below.

**Conformance assets** are only needed for conformance work. Everything builds and all tests pass without them, because the jar and corpus tests skip cleanly with a note, which is exactly how CI runs. The reference jar and the test corpora are deliberately never committed, so they arrive by script and are SHA-verified:

```sh
scripts/bootstrap.sh                    # jar into oracle/ + corpora into corpus/
scripts/bootstrap.sh --with-alloy4fun   # optionally also the 374 MB alloy4fun dataset
scripts/bootstrap.sh --verify           # check everything without fetching
```

## Build and run

```sh
cargo build --release
./target/release/mettle exec corpus/alloytools-models/models/examples/temporal/trash.als
./target/release/mettle serve corpus/alloytools-models/models/examples/systems/file_system.als --command 0
```

`mettle -h` lists the subcommands (`parse`, `check`, `exec` with `--repl`/`--eval`/`--xml`, and `serve`). The browser frontend is plain ES modules embedded via `include_str!`, with no npm and no bundler. Edit `crates/als-sterling/assets/` and rebuild.

## Test

The standard gauntlet. Run it before every PR; all of it must be green:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets   # workspace denies clippy::all + pedantic
cargo test --workspace
cargo doc --workspace --no-deps
```

The conformance tools need the jar and corpora from bootstrap:

```sh
cargo build --release -p als-conform
./target/release/solve-gauge --jobs 8                        # verdict sweep vs cached jar baselines
./target/release/solve-gauge --count --jobs 8                # counting check (add --count-symmetry 20 for the SB-20 one)
./target/release/conform bench                               # speed comparison vs the live jar
```

`solve-gauge` output is deterministic. Capture reports as `> report.txt 2> progress.txt`: stdout is the report and stderr is the live heartbeat, and the two must never be merged. A useful iteration loop is `--only <file>`, which re-runs a single model.

### The CaDiCaL backend

CaDiCaL ([ADR-0019](docs/adr/0019-optional-cadical-backend.md)) is the solver mettle ships. It is part of every build since [ADR-0027](docs/adr/0027-cadical-only-solver.md), so there are no cargo features and no separate passes, and the ordinary `cargo test --workspace` runs its tests. Since mt-124 it is the only backend in the tree; the project's own CDCL was deleted and is recoverable from git history. The build does need a **C++ toolchain**, because it compiles about 100 vendored sources (`vendor/cadical`, see [vendor/README.md](vendor/README.md)). The cross-target determinism battery still runs on tags.

```sh
cargo build --release -p mettle                              # the solver is in the binary
cargo build --release -p als-conform                         # builds `backend-instrument` too

# measure a worklist: per-row CNF size, conflicts spent, encode/solve time.
# --rows takes a newline-separated list of `path[idx]` keys, or `-` to read them
# from stdin, so a slice comes straight out of a sweep report:
python3 -c "import json,sys; d=json.load(open(sys.argv[1])); [print(r['key']) for r in d['per_command'] if r['verdict_bucket'].startswith('agree_')]" report.json \
  | ./target/release/backend-instrument --rows - --conflicts 100000 --wall 600 --jobs 8

# the cross-target determinism battery, locally (compare its output across machines)
./scripts/backend-determinism.sh ./target/release/mettle
```

`exec`, `serve` and `solve-gauge` all take `--solver <name>`. This is the user surface of the backend plugin point ([ADR-0027](docs/adr/0027-cadical-only-solver.md) decision 2), and it stays maintained after the migration: `cadical` is the only name it resolves today, and a backend added later is one variant plus a name. A baseline records which backend produced it, so never compare reports captured under different solvers. Re-capture instead.

### Certifying UNSAT verdicts

An UNSAT verdict can be checked by something that shares none of mettle's code. CaDiCaL logs a **DRAT proof**, mettle writes the solved CNF as DIMACS, and [drat-trim](https://github.com/marijnheule/drat-trim) verifies the one against the other ([ADR-0027](docs/adr/0027-cadical-only-solver.md) decision 4). The checker is dev-side only, never committed and never shipped, and it arrives by script like the jar and the corpora:

```sh
scripts/fetch-drat-trim.sh                                   # builds tools/drat-trim/drat-trim (needs a C compiler)

# certify every UNSAT row the committed sweep baseline agrees with the jar on:
python3 -c "import json,sys; d=json.load(open(sys.argv[1])); [print(k) for k,v in d['entries'].items() if v['verdict_bucket']=='agree_unsat']" baselines/corpus-sweep-sb20.json \
  | ./target/release/backend-instrument --rows - --certify --jobs 8 --out certified.json
```

It exits nonzero if any proof fails to check, and keeps that row's `.cnf`/`.drat`/`.check.txt` for inspection. Everything else is deleted as it goes, because these proofs run to gigabytes across a full audit. Pass `--keep-artifacts` to keep them all, and `--work-dir` to choose where. `sat`, `unknown` and `checker_timeout` rows are reported but do not fail the run, since none of them is evidence against a proof. The budgets default to `solve-gauge`'s own, so a certify run re-derives the sweep's verdicts instead of a differently-budgeted rerun. `--checker-timeout` (default 600s) hard-kills a checker that outlives it.

What a verified proof claims is narrow and worth stating: *this CNF is unsatisfiable*. Whether the CNF faithfully encodes the Alloy command is still the evaluator self-check's job, and the jar's.

## House rules (the short version)

The binding rubrics are **[STYLE.md](STYLE.md)** and **[PORTING_RULES.md](PORTING_RULES.md)**. Read them before writing code. These are the rules that surprise people:

- **Behavior comes from the oracle.** mettle matches the reference Alloy 6.2.0 jar *exactly*. A behavioral change needs evidence from the jar: a probe, a baseline, or a documented rule in [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md). "Seems right" does not ship. Reading the Java and reasoning about it is not evidence. When mettle can't do something yet, it fails loudly with a typed reason and gives no approximate answer.
- **Determinism is non-negotiable.** No wall-clock, no randomness, and no hash-order iteration anywhere near solving, numbering, or output. The same input gives byte-identical output on every machine.
- **Every dependency is justified in writing.** The tree is deliberately tiny. A new crate needs a written case before it goes in.
- **Semantics faithful, structure idiomatic.** We port what the jar *does*. The shape of its Java does not carry over.
- **Every fix pins a regression test**, and non-trivial decisions land as ADRs in [docs/adr/](docs/adr/).

## Finding your way around

[docs/README.md](docs/README.md) is the index. `crates/` is a workspace of 8 crates: `als-syntax` (lex/parse/print) → `als-types` (modules, resolve, typecheck) → `als-core` (relational IR, bounds, encoding, temporal, evaluator) → `als-solve` (the CNF types and the SAT backend interface) → `als-instance` (rendering, XML) / `als-sterling` (serve protocol + frontend assets) → `mettle` (the CLI), plus `als-conform` (the jar-differential test instruments, which are never shipped). [LIMITATIONS.md](LIMITATIONS.md) is the current list of what's missing. If you want to help close something, the issues and `docs/TASKS.md` show what's planned.
