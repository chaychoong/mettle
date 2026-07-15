# mettle — agent operating guide

**mettle** is a ground-up, idiomatic **Rust reimplementation of the Alloy 6 language and analyzer**, shipped as a single static binary (no JVM). It reads standard `.als` files and finds instances/counterexamples, with a first-class CLI, an evaluator REPL, and Sterling-based visualization.

**North Star:** mettle is a **drop-in replacement for the latest Alloy — it does everything Alloy does, exactly.** The one gauge is the **conformance scorecard**: the % of real Alloy models where mettle's answer matches the reference Alloy jar. 100% = drop-in.

> This file is intentionally lean (progressive disclosure). It links to everything; it does not duplicate it.

## Start here (context pickup)
1. Read **[docs/STATE.md](docs/STATE.md)** — the live "where are we right now" doc. Always current.
2. Skim **[docs/TASKS.md](docs/TASKS.md)** — the beads-style task ledger (what's todo/doing/blocked).
3. The full doc map is **[docs/README.md](docs/README.md)**.

## How we work
- **Roles.** The human is product owner: gets updates, asks, reviews, says "proceed." The assistant is **tech lead + coordinator**: owns correctness, sequencing, and taste; delegates volume to sub-agents; keeps the docs and ledger true.
- **Cadence.** Work in reasonable chunks. Stop when a chunk is done or context is getting large. Every stop leaves `docs/STATE.md` accurate so the next session picks up cleanly.
- **Gate at human-testable rungs.** Surface to the human at each rung of **[docs/ROADMAP.md](docs/ROADMAP.md)** with a build they can run and one thing to look for. Don't ask them to review engineering.

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
