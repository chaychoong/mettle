# Contributing to mettle

Thanks for looking under the hood. Two kinds of contribution matter most, in this order:

1. **Divergence reports** — you found a model where mettle and the reference Alloy Analyzer disagree. You don't need any of the setup below for this: see ["Found a difference from Alloy?"](README.md#found-a-difference-from-alloy) in the README and file an issue.
2. **Code and docs** — the rest of this file.

## Workspace setup

You need Rust (the exact toolchain is pinned) and, for the conformance tooling, a JDK.

**Option A — nix (hermetic, recommended):**

```sh
nix develop      # exact rustc 1.97.0 (from rust-toolchain.toml) + JDK 21 + tools
```

**Option B — rustup:**

```sh
rustup show      # rustup auto-installs the pinned toolchain from rust-toolchain.toml
# plus a JDK 21 from wherever you like, if you'll run the jar-backed tools
```

Then fetch the git-ignored assets (the reference jar and the test corpora — both SHA-verified, both deliberately never committed):

```sh
scripts/bootstrap.sh                    # jar into oracle/ + corpora into corpus/
scripts/bootstrap.sh --with-alloy4fun   # optionally also the 374 MB alloy4fun dataset
scripts/bootstrap.sh --verify           # check everything without fetching
```

Everything builds and most tests run **without** the jar and corpora — tests that need them skip cleanly with a note (that's how CI runs). You only need them for conformance work.

## Build and run

```sh
cargo build --release
./target/release/mettle exec corpus/alloytools-models/models/examples/temporal/trash.als
./target/release/mettle serve corpus/alloytools-models/models/examples/systems/file_system.als --command 0
```

`mettle -h` lists the subcommands (`parse`, `check`, `exec` with `--repl`/`--eval`/`--xml`, `serve`). The browser frontend is plain ES modules embedded via `include_str!` — no npm, no bundler; edit `crates/als-sterling/assets/` and rebuild.

## Test

The standard gauntlet — run it before every PR; all of it must be green:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets   # workspace denies clippy::all + pedantic
cargo test --workspace
cargo doc --workspace --no-deps
```

The conformance gauges (need the jar/corpora from bootstrap):

```sh
cargo build --release -p als-conform
./target/release/solve-gauge --jobs 8                        # verdict sweep vs cached jar baselines
./target/release/solve-gauge --count --jobs 8                # counting net (add --count-symmetry 20 for the SB-20 net)
./target/release/conform bench                               # speed comparison vs the live jar
```

`solve-gauge` output is deterministic: capture reports as `> report.txt 2> progress.txt` (stdout is the report, stderr is the live heartbeat — never merge them). A useful iteration loop is `--only <file>` to re-run a single model.

## House rules (the short version)

The binding rubrics are **[STYLE.md](STYLE.md)** and **[PORTING_RULES.md](PORTING_RULES.md)** — read them before writing code. The rules that surprise people:

- **Behavior is pinned by the oracle, not by inspection.** mettle matches the reference Alloy 6.2.0 jar *exactly*. A behavioral change needs evidence from the jar (a probe, a baseline, a documented rule in [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md)) — "seems right" doesn't ship. When mettle can't do something yet, it fails loudly and typed, never approximately.
- **Determinism is non-negotiable.** No wall-clock, no randomness, no hash-order iteration anywhere near solving, numbering, or output. Same input → byte-identical output, on every machine.
- **Every dependency is justified in writing.** The tree is deliberately tiny; a new crate needs a written case, not just a `cargo add`.
- **Semantics faithful, structure idiomatic.** We port what the jar *does*, never how its Java is shaped.
- **Every fix pins a regression test**, and non-trivial decisions land as ADRs in [docs/adr/](docs/adr/).

## Finding your way around

[docs/README.md](docs/README.md) is the index. `crates/` is a workspace of 8 crates: `als-syntax` (lex/parse/print) → `als-types` (modules, resolve, typecheck) → `als-core` (relational IR, bounds, encoding, temporal, evaluator) → `als-solve` (the zero-dep CDCL solver) → `als-instance` (rendering, XML) / `als-sterling` (serve protocol + frontend assets) → `mettle` (the CLI) — plus `als-conform` (the jar-differential test instruments; never shipped). [LIMITATIONS.md](LIMITATIONS.md) is the honest list of what's missing; if you want to help close something, the issues and `docs/TASKS.md` show what's planned.
