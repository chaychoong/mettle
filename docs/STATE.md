# Current state

> The live "where are we" doc. Update this at the end of every work chunk. On pickup, read this first.

**Last updated:** 2026-07-15
**Current rung:** Pre-Rung-1 (foundations / plumbing — see [ROADMAP.md](ROADMAP.md))
**Conformance scorecard:** not yet applicable (no solving implemented)

## What exists
- Repo initialized at `~/repos/mettle` (git, not yet published to a remote).
- Documentation spine: `CLAUDE.md`, `docs/` (this index, STATE, ROADMAP, TASKS, ADRs 0001–0004), `LIMITATIONS.md`, `SEMANTICS_LEDGER.md` scaffold.
- **Binding steering rubrics:** `STYLE.md` + `PORTING_RULES.md` (drafted by an Opus agent, tech-lead reviewed and accepted; numbered rules D#/I#/E#/R# citable in review).
- Toolchains installed in this VM: **Rust stable** (rustup, `~/.cargo/bin`) and **OpenJDK 21** (to drive the reference oracle).

## In flight (delegated, background)
- **Oracle reference brief** (`general-purpose`, `sonnet`) → downloading + empirically verifying the pinned Alloy 6 jar and the exact headless command lines (verdict, counting, `symmetryBreaking=0`, overflow default, SAT4J). Output: `docs/reference/alloy6-reference.md`. *On completion: tech-lead review, then fold exact version/SHA into [ADR-0002](adr/0002-conformance-oracle.md).*

## Not yet started
- Rust workspace + `als-*` crate skeleton and hand-designed core IR types.
- Conformance harness (`als-conform`) that drives the jar and emits the scorecard.
- Corpora vendoring (AlloyTools examples, Alloy4Fun, Portus 63, Kodkod tests).

## Next chunk (planned)
1. Review the two in-flight agent outputs; fold oracle facts into ADR-0002; make the steering docs binding.
2. Lay down the Cargo workspace + empty `als-*` crates matching the DAG in [ROADMAP.md](ROADMAP.md) / plan §3, with CI (fmt + clippy) green.
3. Begin the conformance harness against the pinned jar → first scorecard (of the jar against itself / `expect` annotations) — pure plumbing, not surfaced to the human.

Then: **Rung 1** (parser) is the first build the human is asked to try.

## Open questions for the human (non-blocking)
None currently blocking — the tech lead has taken the standing technical forks (see ADR-0002, ADR-0003). The human is pulled in at Rung 1.
