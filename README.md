# mettle

[![CI](https://github.com/chaychoong/mettle/actions/workflows/ci.yml/badge.svg)](https://github.com/chaychoong/mettle/actions/workflows/ci.yml)
[![Latest release](https://img.shields.io/github/v/release/chaychoong/mettle)](https://github.com/chaychoong/mettle/releases)

**A conformance-tested reimplementation of Alloy 6 as a single self-contained binary.** It needs no Java runtime. mettle reads standard `.als` files, the same language as the reference Alloy Analyzer. It finds instances and counterexamples, steps through temporal traces, and shows all of it in your browser, from a first-class CLI. It tracks **Alloy 6.2.0**, the latest release of the reference implementation.

<picture>
  <source srcset="docs/screenshots/graph-dark.png" media="(prefers-color-scheme: dark)">
  <img src="docs/screenshots/graph-light.png" alt="mettle's graph view: a file_system.als counterexample rendered as a layered graph with per-signature hues and a skolem witness, next to the evaluator pane">
</picture>

> ⚠️ **Zero-versioned by intention.** mettle stays on 0.x because it is not yet meant to be production-ready. The version number makes no claim about how close it is; the scorecard below says that. The aim is to be Alloy exactly, and to earn the right to diverge later. See [what it can and can't do yet](LIMITATIONS.md) and the [roadmap](docs/ROADMAP.md).

## Usage

### Install

Binary releases cover macOS (arm64, x86_64) and Linux (arm64, x86_64). There are no runtime dependencies.

```sh
# homebrew
brew install chaychoong/tap/mettle

# shell installer
curl -LsSf https://github.com/chaychoong/mettle/releases/latest/download/mettle-installer.sh | sh

# nix
nix run github:chaychoong/mettle -- --help

# docker
docker pull ghcr.io/chaychoong/mettle

# from source (the toolchain version is fixed by rust-toolchain.toml)
cargo build --release
```

`cargo install` from crates.io is deliberately not a channel.

mettle solves with **CaDiCaL** ([ADR-0027](docs/adr/0027-cadical-only-solver.md)), built from sources vendored in `vendor/cadical`, so a build from source needs a C++ toolchain. `exec` and `serve` take `--solver <name>` to pick the SAT backend, and `cadical` is the one name it accepts today. What that costs is written up in [LIMITATIONS.md](LIMITATIONS.md).

### Try it

You can run mettle straight from GHCR without installing anything. Point it at any `.als` file:

```sh
# solve every command in a model
docker run --rm -v "$PWD":/work ghcr.io/chaychoong/mettle exec /work/model.als

# visualize one in the browser, then open http://localhost:4030
docker run --rm -p 4030:4030 -v "$PWD":/work ghcr.io/chaychoong/mettle serve /work/model.als --bind 0.0.0.0
```

### What you can run

```sh
# Take every run/check command in the file to a verdict, with instances and
# counterexamples rendered. This includes Alloy 6 temporal models: mettle
# searches for a lasso trace and prints it state by state, with the loop marked.
mettle exec model.als

# An evaluator REPL over the solved instance. On a temporal command it is a
# trace debugger, and `:state N` moves the evaluation point through the loop.
mettle exec model.als --repl

# Solve one command and explore it in the browser: graph and table views, the
# trace rail, an evaluator pane, and New Trace / New Config / New Init /
# New Fork enumeration. It speaks the Sterling provider protocol, so external
# Sterling clients work too.
mettle serve model.als

# Write the solved command as instance XML, in the same byte shape as the
# reference jar's own writer.
mettle exec model.als --xml out.xml

# Parse, resolve, and typecheck, with rustc-style caret diagnostics.
mettle parse model.als
mettle check model.als
```

The temporal trace rail draws the lasso's loop:

<img src="docs/screenshots/trace-rail.png" alt="mettle's trace stepper on a temporal model: a six-state lasso with the amber loop arc marking that state 5 repeats forever">

## The measure of success

mettle's goal is to be a **drop-in replacement for the latest Alloy**. We measure that claim against the reference Alloy 6.2.0 jar, which is fixed at one exact version and SHA-256, and we re-measure on every change. The conformance scorecard below is how we track it: on every model both tools can execute, they must give the same answer. Where mettle cannot execute something yet, it says so and reports `CANNOT EXECUTE` with a reason. It never guesses, so a verdict you get is a verdict that was checked.

## Benchmarks

The correctness figures below were measured on 2026-08-25, the speed figures on 2026-07-27. Both run over the committed corpora (alloytools-models plus portus-63: 167 files, 564 `run`/`check` commands) and regenerate from a checkout, with the commands at the end of this section. Correctness numbers are deterministic, so they come out byte-identical across runs and machines. Timings vary with the machine.

### Correctness

Four independent checks, each a differential comparison against the fixed jar:

| Check | What it does | Result |
|---|---|---|
| **Verdict agreement** | compares every command's SAT/UNSAT verdict with the jar's | **552 of 564 agree (288 SAT / 264 UNSAT), 0 disagreements** |
| **Self-check** | re-verifies every instance mettle emits, using mettle's own independent evaluator | **0 failures** |
| **Counting** | enumerates all solutions at small scopes and counts them against the jar, at two symmetry settings | **69 exact matches at symmetry 0, 93 at symmetry 20, 0 mismatches** |
| **Syntax and resolution** | lex, parse, print and re-parse round-trip, then resolve and typecheck accept/reject against the jar | **167 of 167 files, 100% agreement** |

Of the 12 remaining commands, 2 are commands mettle answers but the jar times out on, so there is nothing to compare. For the other 10, mettle reports a typed reason and gives no verdict: 2 run past the default solve budget, 2 hit a gap in lowering, 4 are higher-order commands the jar also errors on, and 2 are temporal commands mettle rejects with the same text the jar uses. There were **0 panics** across the corpus, as always.

An UNSAT verdict can also be machine-certified: CaDiCaL logs a DRAT proof, and an external checker verifies it against the CNF mettle solved. [CONTRIBUTING.md](CONTRIBUTING.md) has the recipe.

Beyond the corpus, a differential pass over 150,891 snippets from the [Alloy4Fun](https://github.com/haslab/Alloy4Fun) dataset (measured 2026-08-25) found **0 disagreements in either direction**: mettle rejects nothing the jar accepts and accepts nothing the jar rejects, **100.0000% agreement**; error positions match exactly on 99.79% of parse errors. Warning emission matches the jar on 101,969 of the 101,970 files, with the jar's and mettle's warning counts equal. A mutation fuzzer runs 4,248 mutants per CI run, verified to 88,500 offline, and holds three properties: no panic, sane spans, round-trip stable.

Every behavioral rule mettle matches is written down in the [Semantics Ledger](SEMANTICS_LEDGER.md). Every disagreement ever found was root-caused and has a regression test in the tree.

### Speed

Parse plus resolve over the whole 167-file corpus, mettle against the jar's own batch API, measured 2026-07-27:

| | mettle | Alloy jar |
|---|---|---|
| whole corpus, one process | **61.5 ms** | 1,305 ms (warm JVM, startup excluded) |
| median per file | **1.1 ms** | 5.4 ms (in-JVM) / 160 ms (cold JVM, startup included) |

The like-for-like comparison is the batch row, about 21 times faster. Read it as whole-corpus wall clock: mettle's total uses thread parallelism while the jar's batch API is single-threaded, and the bench tool prints this caveat itself. The cold-start column is closer to what interactive use feels like, because mettle is a native binary with no VM to warm up.

Solving is compared for *agreement* under budgets and is never raced. The enumeration and counting checks above bound it: everything the jar answers at small scopes, mettle answers identically, and two corpus temporal commands solve under mettle's budgets where the jar times out.

### Regenerate

```sh
./scripts/fetch-corpora.sh                                  # corpora are fetched, never committed
cargo build --release -p als-conform -p mettle
./target/release/solve-gauge --jobs 8                       # verdict sweep + self-check
./target/release/solve-gauge --count --jobs 8               # counting check, symmetry 0
./target/release/solve-gauge --count --count-symmetry 20 --jobs 8
./target/release/conform bench                              # speed table (needs the jar in oracle/)
cargo test --release -p als-syntax --test corpus_roundtrip  # syntax check
```

## Found a difference from Alloy?

That is the most valuable contribution you can make. mettle's whole claim is "Alloy, exactly", so **any** model where mettle and the Alloy Analyzer disagree is a bug here, however small. That includes a different verdict, a different error, mettle accepting something Alloy rejects, mettle rejecting something Alloy accepts, and any trace or evaluator answer that differs.

1. Check [LIMITATIONS.md](LIMITATIONS.md) first. Every *known* gap and deliberate divergence is listed there, and a `CANNOT EXECUTE` report means mettle declined to answer, so it is not a disagreement.
2. [Open a divergence issue](https://github.com/chaychoong/mettle/issues/new?template=divergence.md) with the smallest `.als` you can make that shows it, the exact command you ran, what Alloy says (version 6.2.0 is the reference), what mettle says, and your `mettle --version`.

Shrinking the model is appreciated and optional. A big model that disagrees is still a real find. Every confirmed divergence gets root-caused and a regression test.

## How it's built, and whether you should use it

This project is built primarily by an AI agent fleet, with a human product owner steering and reviewing. The process itself is checked into the repo, if you are curious how it was run: [CLAUDE.md](CLAUDE.md), the [ADRs](docs/adr/), the human-owned [Semantics Ledger](SEMANTICS_LEDGER.md), and the [task ledger](docs/TASKS.md).

Should you use it? I dogfood mettle, and I like it better than the reference Analyzer, partly because I made it and partly because it feels lighter. You might like it because it installs in seconds and runs anywhere without a JVM. It is a reimplementation, so **there may be behavioral differences from real Alloy that we haven't found yet.** We work to close that gap continually. The scorecard and every check above regenerate from a checkout with one script against the fixed reference jar, and every confirmed divergence gets root-caused and a regression test. The possibility of an unfound difference is always there. Known gaps and deliberate divergences are in [LIMITATIONS.md](LIMITATIONS.md); if you find a new one, [that's the most valuable thing you can hand us](#found-a-difference-from-alloy).

Note: the *product* contains no JVM. The *test infrastructure* deliberately runs the reference Alloy jar to regenerate the scorecard, which is the whole point of it.

## Documentation

Start at **[docs/README.md](docs/README.md)** (index) or **[docs/ROADMAP.md](docs/ROADMAP.md)** (the plan). Current gaps: [LIMITATIONS.md](LIMITATIONS.md). To hack on mettle itself, **[CONTRIBUTING.md](CONTRIBUTING.md)** has the workspace setup, build, and test story.

## License

mettle is **MPL-2.0** ([LICENSE](LICENSE)). The `util/*` standard library is a clean-room rewrite, written against interface descriptions and never against upstream text ([ADR-0006](docs/adr/0006-licensing-posture.md)). The reference Alloy jar is used only as a test oracle, and is never shipped or embedded. Test corpora are fetched locally by script and never redistributed.
