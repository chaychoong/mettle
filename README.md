# mettle

**A conformance-tested reimplementation of Alloy 6 as a single self-contained binary.** No JVM. mettle reads standard `.als` files — the same language as the reference Alloy Analyzer — finds instances and counterexamples, steps through temporal traces, and visualizes it all in your browser, from a first-class CLI. It tracks **Alloy 6.2.0** (the latest release of the reference implementation); mettle's own version number is independent, with 1.0.0 reserved for verified drop-in parity.

<picture>
  <source srcset="docs/screenshots/graph-dark.png" media="(prefers-color-scheme: dark)">
  <img src="docs/screenshots/graph-light.png" alt="mettle's graph view: a file_system.als counterexample rendered as a layered graph with per-signature hues and a skolem witness, next to the evaluator pane">
</picture>

> ⚠️ **Pre-1.0.** mettle is a feature-complete candidate under review. It is deliberately *not* "Alloy but better" — it aims to be **Alloy, exactly**, then earn the right to diverge. See [what it can and can't do yet](LIMITATIONS.md) and the [roadmap](docs/ROADMAP.md).

## Try it

No install, straight from GHCR — point it at any `.als` file:

```sh
# solve every command in a model
docker run --rm -v "$PWD":/work ghcr.io/chaychoong/mettle exec /work/model.als

# visualize one in the browser (then open http://localhost:4030)
docker run --rm -p 4030:4030 -v "$PWD":/work ghcr.io/chaychoong/mettle serve /work/model.als --bind 0.0.0.0
```

Prefer a native binary? See [Install](#install) below.

## What you can run today

- `mettle exec model.als` — every `run`/`check` command to a verdict, instances and counterexamples rendered — including Alloy 6 temporal models: lasso-trace search with the loop marked, state by state.
- `mettle exec model.als --repl` — an evaluator REPL over the solved instance; on a temporal command it is a trace debugger (`:state N` moves the evaluation point through the loop).
- `mettle serve model.als` — solve one command and explore it in the browser: graph and table views, the trace rail, an evaluator pane, and New&nbsp;Trace / New&nbsp;Config / New&nbsp;Init / New&nbsp;Fork enumeration. Speaks the Sterling provider protocol, so external Sterling clients work too.
- `mettle exec model.als --xml out.xml` — the solved command as instance XML, byte-shaped like the reference jar's own writer.
- `mettle parse` / `mettle check` — parse, resolve, and typecheck with rustc-style caret diagnostics.

The temporal trace rail, with the lasso's loop drawn rather than implied:

<img src="docs/screenshots/trace-rail.png" alt="mettle's trace stepper on a temporal model: a six-state lasso with the amber loop arc marking that state 5 repeats forever">

## The measure of success

mettle's goal is to be a **drop-in replacement for the latest Alloy**. That claim is not asserted — it is **measured**, continuously, against the reference Alloy 6.2.0 jar (pinned by exact version and SHA-256). The one gauge that matters is the conformance scorecard below: on every model both tools can execute, they must give the same answer. Where mettle cannot yet execute something, it says so with a typed `CANNOT EXECUTE` — it never guesses, so a verdict you get is a verdict that was checked.

## Benchmarks

All figures below were measured 2026-07-27 on the committed corpora (alloytools-models + portus-63: 167 files, 564 `run`/`check` commands) and are regenerable from a checkout — commands at the end of this section. Correctness numbers are deterministic (byte-identical across runs and machines); timings are timings.

### Correctness

Four independent nets, all differential against the pinned jar:

| Net | What it checks | Result |
|---|---|---|
| **Verdict agreement** | every command's SAT/UNSAT verdict vs 549 cached jar verdicts | **356 agreements (203 SAT / 153 UNSAT), 0 disagreements** |
| **Self-check** | every instance mettle emits, re-verified by mettle's own independent evaluator | **0 failures** |
| **Counting** | *all* solutions enumerated at small scopes and counted vs the jar, at two symmetry settings | **56 exact matches (SB=0) / 79 (SB=20), 0 mismatches** |
| **Syntax & resolution** | lex → parse → print → re-parse round-trip, then resolve/typecheck accept/reject vs the jar | **167/167 files, 100% agreement** |

The remaining commands are honest, *typed* defers, never wrong answers: 117 beyond the default capacity ceiling, 62 beyond the default solve budget (deeper budgets convert more — 0 disagreements at every depth tried), 7 known unsupported corners (documented in [LIMITATIONS.md](LIMITATIONS.md)), 6 where mettle types out with the same rejection the jar itself gives, and 16 where the jar produces no verdict at all. **0 panics** across the corpus, always.

Beyond the corpus: a 150,891-snippet differential parse pass against the [Alloy4Fun](https://github.com/haslab/Alloy4Fun) dataset found **zero cases where the jar accepts and mettle rejects** and 99.79% exact agreement on error positions; warning emission matches the jar on 99.80% of files (both measured 2026-07); and a mutation fuzzer (~4,200 mutants per CI run, verified to 88,500 offline) holds three properties: no panic, sane spans, round-trip stable.

Every behavioral rule mettle matches is written down in the [Semantics Ledger](SEMANTICS_LEDGER.md); every disagreement ever found was root-caused and is pinned by a regression test in-tree.

### Speed

Parse + resolve over the whole 167-file corpus, mettle vs the jar's own batch API:

| | mettle | Alloy jar |
|---|---|---|
| whole corpus, one process | **61.5 ms** | 1,305 ms (warm JVM, startup excluded) |
| median per file | **1.1 ms** | 5.4 ms (in-JVM) / 160 ms (cold JVM, startup included) |

The like-for-like comparison is the batch row (~21× — though mettle's total uses thread parallelism while the jar's batch API is single-threaded, so read it as "whole-corpus wall clock", not single-core speed; the bench tool prints this caveat itself). The cold-start column is what interactive use feels like: mettle is a native binary with no VM to warm up.

Solving is compared for *agreement* under budgets, not raced — but the enumeration and counting nets above bound it: everything the jar answers at small scopes, mettle answers identically, and two corpus temporal commands solve under mettle's budgets where the jar times out.

### Regenerate

```sh
./scripts/fetch-corpora.sh                                  # corpora are fetched, never committed
cargo build --release -p als-conform -p mettle
./target/release/solve-gauge --jobs 8                       # verdict sweep + self-check
./target/release/solve-gauge --count --jobs 8               # counting net, symmetry 0
./target/release/solve-gauge --count --count-symmetry 20 --jobs 8
./target/release/conform bench                              # speed table (needs the jar in oracle/)
cargo test --release -p als-syntax --test corpus_roundtrip  # syntax net
```

## Install

Binary releases cover macOS (arm64, x86_64) and Linux (arm64, x86_64); no JVM, no runtime dependencies.

```sh
# homebrew
brew install chaychoong/tap/mettle

# shell installer
curl -LsSf https://github.com/chaychoong/mettle/releases/latest/download/mettle-installer.sh | sh

# nix
nix run github:chaychoong/mettle -- --help

# from source (toolchain pinned by rust-toolchain.toml)
cargo build --release
```

`cargo install` from crates.io is deliberately not a channel.

## Found a difference from Alloy?

That's the most valuable contribution you can make. mettle's whole claim is "Alloy, exactly" — so **any** model where mettle and the Alloy Analyzer disagree (different verdict, different error, mettle accepts something Alloy rejects or vice versa, a trace or evaluator answer that differs) is a bug here, however small.

1. Check [LIMITATIONS.md](LIMITATIONS.md) first — every *known* gap and deliberate divergence is listed there, and a typed `CANNOT EXECUTE` is mettle declining honestly, not disagreeing.
2. [Open a divergence issue](https://github.com/chaychoong/mettle/issues/new?template=divergence.md) with the smallest `.als` you can make that shows it, the exact command you ran, what Alloy says (version 6.2.0 is the reference), what mettle says, and your `mettle --version`.

Shrinking the model is appreciated but optional — a big model that disagrees is still a real find. Every confirmed divergence gets root-caused and pinned by a regression test.

## How it's built, and whether you should use it

This project is built primarily by an AI agent fleet, with a human product owner steering and reviewing. The process itself is checked into the repo — [CLAUDE.md](CLAUDE.md), the [ADRs](docs/adr/), the human-owned [Semantics Ledger](SEMANTICS_LEDGER.md), the [task ledger](docs/TASKS.md) — if you're curious how it was run.

Should you use it? The honest version: I dogfood mettle, and I like it better than the reference Analyzer — partly because I made it, and partly because it feels lighter. You might like it because it installs in seconds and runs anywhere without a JVM. But it *is* a reimplementation, and **there may be behavioral differences from real Alloy that we haven't found yet.** We work to close that gap continually — the scorecard and every net above regenerate from a checkout with one script against the pinned reference jar, and every confirmed divergence gets root-caused and pinned by a regression test — but the possibility is always there. Known gaps and deliberate divergences are in [LIMITATIONS.md](LIMITATIONS.md); if you find a new one, [that's the most valuable thing you can hand us](#found-a-difference-from-alloy).

Note: the *product* contains no JVM. The *test infrastructure* deliberately runs the reference Alloy jar to regenerate the scorecard — that's the point.

## Documentation

Start at **[docs/README.md](docs/README.md)** (index) or **[docs/ROADMAP.md](docs/ROADMAP.md)** (the plan). Honest current gaps: [LIMITATIONS.md](LIMITATIONS.md). Want to hack on mettle itself? **[CONTRIBUTING.md](CONTRIBUTING.md)** has the workspace setup, build, and test story.

## License

mettle is **MPL-2.0** ([LICENSE](LICENSE)). The `util/*` standard library is a clean-room rewrite (written against interface descriptions, never upstream text — [ADR-0006](docs/adr/0006-licensing-posture.md)). The reference Alloy jar is used only as a test oracle and is never shipped or embedded; test corpora are fetched locally by script and never redistributed.
