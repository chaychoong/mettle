# mettle — agent operating guide

**mettle** is a ground-up, idiomatic **Rust reimplementation of the Alloy 6 language and analyzer**, shipped as a single static binary (no JVM). It reads standard `.als` files and finds instances/counterexamples, with a first-class CLI, an evaluator REPL, and Sterling-based visualization.

**North Star:** mettle is a **drop-in replacement for the latest Alloy — it does everything Alloy does, exactly.** The one gauge is the **conformance scorecard**: the % of real Alloy models where mettle's answer matches the reference Alloy jar. 100% = drop-in.

> This file is intentionally lean (progressive disclosure). It links to everything; it does not duplicate it.

## Start here — resuming, and what "proceed" means
A bare **"proceed"** from the product owner (or any resume with no specifics) means: **do the "Next chunk" in [docs/STATE.md](docs/STATE.md).** Don't ask what to work on — STATE.md is authoritative and is kept current at every stop. Concretely, on cold pickup:
1. Read **[docs/STATE.md](docs/STATE.md)** — the live "where are we" doc: current rung, what exists, decided vs. open questions, and the **Next chunk** to start. This is the single source of truth for "what now".
2. Skim **[docs/TASKS.md](docs/TASKS.md)** — the beads ledger; the `◐ doing` bead and the next `▢` beads are the work, with dependencies.
3. Before writing any code, obey the rubrics: **[STYLE.md](STYLE.md)**, **[PORTING_RULES.md](PORTING_RULES.md)**, and only `approved` entries in **[SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md)**.
4. Full doc map: **[docs/README.md](docs/README.md)**. Recent decisions and rationale: **[docs/adr/](docs/adr/)**.

Then just start the Next chunk and report at the product level when it's a meaningful checkpoint.

## Operating contract (binding)
- **Roles.** The human is **product owner**: gets updates, asks questions, reviews, and says "proceed." That's the whole job. The assistant is **tech lead + coordinator**: owns correctness, sequencing, taste, and standing technical decisions; delegates volume to sub-agents; keeps the docs and ledger true. The human is not asked to review engineering — only to test at rungs.
- **Gate only at human-testable rungs.** Surface to the human at each rung of **[docs/ROADMAP.md](docs/ROADMAP.md)** with a build they can run and one concrete thing to look for. Between rungs, work heads-down.
- **Talk at the product level.** Progress is reported as "here's what you can now run," not as engineering internals. The scorecard is the shared gauge.
- **Chunks + clean handoff.** Work in reasonable chunks. Stop when a chunk is done or context is getting large/bloated. **Every stop leaves [docs/STATE.md](docs/STATE.md) accurate** so the next session picks up cold with no context loss. **Before ending a session, run the wrap routine — [docs/SESSION_WRAP.md](docs/SESSION_WRAP.md)** (commit everything, make the docs true, file the lessons).
- **Commit cadence.** Commit at the end of each work chunk, [scopedcommits](docs/adr/) style (`scope(subscope): imperative title`), **no AI attribution** (no "Generated with…" line, no `Co-Authored-By`). Reference beads by id (`mt-NNN`). Git history is part of the referenceable handoff.
- **Delegate volume, stay coordinator.** Push coding/research to sub-agents (see Delegation policy below); the tech lead writes the spec, reviews against the rubrics, and owns the merge — never rubber-stamps.
- **Discipline the human asked for, in one line:** correctness first · no unnecessary tech debt · idiomatic Rust · live docs + ADRs, all cross-linked (nothing orphaned) · lean progressively-disclosed CLAUDE.md · a maintained task ledger.

## Principles (the short version — full rubric in [STYLE.md](STYLE.md))
- **Correctness first. No unnecessary tech debt. Idiomatic Rust.**
- Determinism is non-negotiable (fixed solver build → byte-identical output; no HashMap iteration near numbering/output).
- Assert invariants, including negative space.
- Semantics faithful, structure idiomatic — never port Java structure. See [PORTING_RULES.md](PORTING_RULES.md).
- Arena discipline (index-based IRs, typed IDs; no `Rc<RefCell>` graphs).
- Every dependency justified in writing. Spans + temporal syntax from day one.

## Behavior is pinned by an oracle, not by inspection
The reference Alloy jar is the yardstick. Faithful behavioral rules live in the human-owned **[SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md)**; agents implement *from the Ledger*, never from vibes. Honest current gaps live in **[LIMITATIONS.md](LIMITATIONS.md)**.

## Delegation policy
- Delegate coding/research to sub-agents; **always name the model** and say why (research/verify-heavy → `sonnet`; foundational/taste-heavy or subtle correctness → `opus`; cheap mechanical → `haiku`).
- The tech lead stays coordinator: writes specs, reviews against the rubrics ([STYLE.md](STYLE.md), [PORTING_RULES.md](PORTING_RULES.md), [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md)), owns merges.

## Decisions are recorded
Every non-trivial decision is an ADR in **[docs/adr/](docs/adr/)**. Superseded ADRs are marked, not deleted. No doc is orphaned — everything is reachable from [docs/README.md](docs/README.md).
