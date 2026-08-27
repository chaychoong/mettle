# Contributing to mettle

## Contribution priorities

1. Report divergences first. A divergence is a model where mettle and the reference Alloy Analyzer 6.2.0 jar disagree. You need none of the setup below. See [Found a difference from Alloy](README.md#found-a-difference-from-alloy) and the issue tracker.
2. Contribute code and documentation.

## Set up the workspace

Nix provides the exact rustc 1.97.0, JDK 21, and every tool used by the scripts.

```sh
nix develop
```

Without Nix, install these prerequisites:

- Rust through rustup. `rust-toolchain.toml` selects the version automatically.
- JDK 21 for jar-backed conformance tools. Plain builds and tests need no Java.
- git, curl, and python3 for the asset-fetch script.

Conformance assets are needed only for conformance work. Everything builds and all tests pass without them. Jar and corpus tests skip with a note, as they do in CI.

The reference jar and test corpora are never committed. The script fetches them and verifies their SHA values.

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

`mettle -h` lists `parse`, `check`, `exec`, and `serve`. The `exec` command supports `--repl`, `--eval`, and `--xml`.

The browser frontend uses plain ES modules embedded through `include_str!`. It has no npm or bundler. Edit `crates/als-sterling/assets/`, then rebuild.

## Run the test gauntlet

Run every standard check before each PR.

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets   # workspace denies clippy::all + pedantic
cargo test --workspace
cargo doc --workspace --no-deps
```

The conformance tools need the jar and corpora from `scripts/bootstrap.sh`.

```sh
cargo build --release -p als-conform
./target/release/solve-gauge --jobs 8                        # verdict sweep vs cached jar baselines
./target/release/solve-gauge --count --jobs 8                # counting check (add --count-symmetry 20 for the SB-20 one)
./target/release/conform bench                               # speed comparison vs the live jar
./target/release/conform bench --solve                       # per-command solve head-to-head vs the live jar
```

`solve-gauge` output is deterministic. Capture reports as `> report.txt 2> progress.txt`. Standard output holds the report. Standard error holds the live heartbeat. Never merge them.

Use `--only <file>` to run one model again during development.

## Work with the CaDiCaL backend

CaDiCaL is the solver in every build since [ADR-0027](docs/adr/0027-cadical-only-solver.md). The earlier optional-backend decision is [ADR-0019](docs/adr/0019-optional-cadical-backend.md).

The tree has one backend since mt-124. The project's own CDCL was deleted and remains available in git history.

The backend has no cargo features or separate test passes. `cargo test --workspace` runs its tests.

The build needs a C++ toolchain. It compiles about 100 vendored sources in `vendor/cadical`. See [vendor/README.md](vendor/README.md).

The cross-target determinism battery runs on tags.

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

`exec`, `serve`, and `solve-gauge` accept `--solver <name>`. This flag is the backend plugin point from ADR-0027 decision 2. `cadical` is the only name resolved today. A later backend needs one variant and one name.

A baseline records its backend. Never compare reports from different solvers. Capture a new report instead.

## Certify UNSAT verdicts

A checker that shares none of mettle's code can verify an UNSAT verdict. CaDiCaL logs a DRAT proof. mettle writes the solved CNF as DIMACS. [drat-trim](https://github.com/marijnheule/drat-trim) checks the proof against the CNF, as set by ADR-0027 decision 4.

The checker is for development only. It is never committed or shipped. Fetch it with the script.

```sh
scripts/fetch-drat-trim.sh                                   # builds tools/drat-trim/drat-trim (needs a C compiler)

# certify every UNSAT row the committed sweep baseline agrees with the jar on:
python3 -c "import json,sys; d=json.load(open(sys.argv[1])); [print(k) for k,v in d['entries'].items() if v['verdict_bucket']=='agree_unsat']" baselines/corpus-sweep-sb20.json \
  | ./target/release/backend-instrument --rows - --certify --jobs 8 --out certified.json
```

The command exits nonzero if any proof fails. It keeps that row's `.cnf`, `.drat`, and `.check.txt` files for inspection. It deletes other artifacts during the run because a full audit produces gigabytes of proofs.

Use `--keep-artifacts` to keep every artifact. Use `--work-dir` to choose their directory.

Rows marked `sat`, `unknown`, or `checker_timeout` appear in the report but do not fail the run. None provides evidence against a proof.

The budgets default to those used by `solve-gauge`. The certification run therefore derives the sweep verdicts again. `--checker-timeout` (default 600 s) hard-kills a checker that outlives it.

A verified proof establishes that the CNF is unsatisfiable. The evaluator self-check and the jar test whether the CNF faithfully encodes the Alloy command.

## Follow the house rules

Read [STYLE.md](STYLE.md) and [PORTING_RULES.md](PORTING_RULES.md) before writing code.

Behavior comes from the oracle. mettle matches the jar exactly. A behavioral change needs evidence from the jar. Use a probe, a baseline, or a documented rule in the [Semantics Ledger](SEMANTICS_LEDGER.md). Reading the Java and reasoning about it is not evidence.

When mettle cannot handle a construct, return a typed reason. Do not return an approximate answer.

Keep output deterministic. Do not use wall-clock data, randomness, or hash-order iteration near solving, numbering, or output. The same input must produce byte-identical output on every machine.

Justify every dependency in writing. The dependency tree is deliberately tiny. Keep semantics faithful and code structure idiomatic. Port the jar's behavior, not its Java structure.

Add a regression test for every fix. Record non-trivial decisions as ADRs in `docs/adr/`.

## Find code and plans

[docs/README.md](docs/README.md) is the documentation index.

The `crates/` workspace contains 8 crates.

`als-syntax` handles lexing, parsing, and printing. `als-types` handles modules, resolution, and type checking. `als-core` holds relational IR, bounds, encoding, temporal logic, and the evaluator. `als-solve` holds CNF types and the SAT backend interface.

`als-instance` handles rendering and XML. `als-sterling` holds the serve protocol and frontend assets. `mettle` is the CLI. `als-conform` contains jar-differential test instruments and is never shipped.

[LIMITATIONS.md](LIMITATIONS.md) lists missing behavior. Issues and [docs/TASKS.md](docs/TASKS.md) show planned work.
