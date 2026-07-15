# Current state

> The live "where are we" doc. Update this at the end of every work chunk. On pickup, read this first.

**Last updated:** 2026-07-15
**Current rung:** Pre-Rung-1 (foundations / plumbing — see [ROADMAP.md](ROADMAP.md))
**Conformance scorecard:** not yet applicable (no solving implemented)

## What exists
- Repo initialized at `~/repos/mettle` (git, not yet published to a remote).
- Documentation spine: `CLAUDE.md`, `docs/` (this index, STATE, ROADMAP, TASKS, ADRs 0001–0004), `LIMITATIONS.md`, `SEMANTICS_LEDGER.md` scaffold.
- **Binding steering rubrics:** `STYLE.md` + `PORTING_RULES.md` (drafted by an Opus agent, tech-lead reviewed and accepted; numbered rules D#/I#/E#/R# citable in review).
- **Pinned conformance oracle:** Alloy **6.2.0**, jar SHA-256 `6b8c1cb5…edb78d`, recorded in [ADR-0002](adr/0002-conformance-oracle.md) + [reference/alloy6-reference.md](reference/alloy6-reference.md). Headless invocation empirically proven (verdict, count, SB=0 via `A4Options` API, SAT4J zero-native-deps, `expect` semantics). Jar lives in git-ignored `oracle/`.
- Toolchains installed in this VM: **Rust stable** (rustup, `~/.cargo/bin`) and **OpenJDK 21** (to drive the reference oracle).

## In flight (delegated, background)
- _None._ Both Pre-Rung-1 delegations (steering docs, oracle brief) are complete and reviewed.

## Not yet started
- Rust workspace + `als-*` crate skeleton and hand-designed core IR types.
- Conformance harness (`als-conform`) that drives the jar and emits the scorecard.
- Corpora vendoring (AlloyTools examples, Alloy4Fun, Portus 63, Kodkod tests).

## Next chunk (planned)
1. Lay down the Cargo workspace + empty `als-*` crates matching the DAG in [ROADMAP.md](ROADMAP.md) / plan §3, with CI (fmt + clippy) green. (mt-004 → mt-005)
2. Begin the conformance harness against the pinned jar → first scorecard (jar vs. `expect` annotations, Net 0) — pure plumbing, not surfaced to the human. Build on the `A4Options` Java shim, not the buggy `exec -y` flag (see mt-006 note). (mt-006, mt-007)

Then: **Rung 1** (parser) is the first build the human is asked to try.

## Open questions for the human (non-blocking)
- **LEDGER-001 — overflow default.** Alloy 6.2.0's overflow default differs by entry point (GUI = forbid, headless = allow). mettle must pick one canonical default. Tech lead recommends **forbid** (match the GUI users know); awaiting product-owner blessing. Not blocking until Rung 3 (integers). See [SEMANTICS_LEDGER.md](../SEMANTICS_LEDGER.md).
- **Licensing (mt-008).** Upstream Alloy's license is unsettled; mettle's own attribution/NOTICE + how `util/*.als` is vendored need a licensing ADR before any derived text ships. Not blocking pre-corpus work.
