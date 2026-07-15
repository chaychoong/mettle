# Current state

> The live "where are we" doc. Update this at the end of every work chunk. On pickup, read this first.

**Last updated:** 2026-07-15
**Current rung:** Pre-Rung-1 (foundations / plumbing — see [ROADMAP.md](ROADMAP.md))
**Conformance scorecard:** not yet applicable (no solving implemented)
**Builds:** `cargo build/fmt/clippy/test` all green on the empty workspace.

## What exists
- Repo initialized at `~/repos/mettle` (git, not yet published to a remote).
- Documentation spine: `CLAUDE.md`, `docs/` (this index, STATE, ROADMAP, TASKS, ADRs 0001–0004), `LIMITATIONS.md`, `SEMANTICS_LEDGER.md`. Session routines: pickup in `CLAUDE.md` → "Start here"; close via `docs/SESSION_WRAP.md`; lessons in `docs/LESSONS.md`.
- **Binding steering rubrics:** `STYLE.md` + `PORTING_RULES.md` (drafted by an Opus agent, tech-lead reviewed and accepted; numbered rules D#/I#/E#/R# citable in review).
- **Pinned conformance oracle:** Alloy **6.2.0**, jar SHA-256 `6b8c1cb5…edb78d`, recorded in [ADR-0002](adr/0002-conformance-oracle.md) + [reference/alloy6-reference.md](reference/alloy6-reference.md). Headless invocation empirically proven (verdict, count, SB=0 via `A4Options` API, SAT4J zero-native-deps, `expect` semantics). Jar lives in git-ignored `oracle/`.
- **Cargo workspace skeleton (mt-004):** 8 crates on the hand-designed DAG — `als-syntax`, `als-solve` (no deps); `als-types`→syntax; `als-core`→syntax/types/solve; `als-instance`→syntax/types/core/solve; `als-sterling`→types/instance; `als-conform`→syntax; `mettle` binary→all six libs. Workspace lints forbid `unsafe`, deny `clippy::all`, warn `pedantic`. CI at `.github/workflows/ci.yml`. All gates green.
- Toolchains installed in this VM: **Rust stable** (rustup + rustfmt + clippy, `~/.cargo/bin`) and **OpenJDK 21** (to drive the reference oracle).

## In flight (delegated, background)
- _None._ All Pre-Rung-1 delegations (steering docs, oracle brief, workspace skeleton) complete and reviewed.

## Not yet started
- Rust workspace + `als-*` crate skeleton and hand-designed core IR types.
- Conformance harness (`als-conform`) that drives the jar and emits the scorecard.
- Corpora vendoring (AlloyTools examples, Alloy4Fun, Portus 63, Kodkod tests).

## Next chunk (planned)
**On "proceed", start mt-005 directly** (it's the tech-lead design pass, not delegable). mt-006/007 can run *concurrently* as background sub-agent delegations — they depend only on done mt-002/mt-004, not on mt-005 — but mt-005 is the priority and gets your own focus.

1. **mt-005 — hand-design the core IR/AST types** (tech-lead-authored, do directly): typed-index arena IDs and the core AST + relational-IR type skeletons across `als-syntax`/`als-core`. The load-bearing design pass; deserves a fresh, focused context. Per STYLE §6 (arena discipline) + PORTING_RULES R3.
2. **mt-006/007 — conformance harness + corpora** (delegable, in parallel): drive the pinned jar (via the `A4Options` shim, not the buggy `exec -y`; `-s sat4j`; temp workdir) → first scorecard (jar vs. `expect` annotations, Net 0). Pure plumbing, not surfaced to the human. (mt-007 corpora vendoring is gated by the mt-008 licensing question for anything shipped, but mining verdicts for the scorecard is fine.)

Then: **Rung 1** (parser) is the first build the human is asked to try.

## Recent decisions
- **LEDGER-001 — overflow default = FORBID** (approved 2026-07-15, matches the Alloy GUI experience). Build toward this; `--[no-]overflow` flag toggles it. Harness sets the oracle to match.

## Open questions for the human (non-blocking)
- **Licensing (mt-008).** Upstream Alloy's license is unsettled; mettle's own attribution/NOTICE + how `util/*.als` is vendored need a licensing ADR before any derived text ships. Not blocking pre-corpus work.
