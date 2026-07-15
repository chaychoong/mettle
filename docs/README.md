# mettle documentation index

Every doc in the project is reachable from here. Nothing is orphaned. Superseded docs are marked, not deleted.

## Live state (always current)
- **[STATE.md](STATE.md)** — where we are right now; read this first on pickup.
- **[ROADMAP.md](ROADMAP.md)** — the North Star and the human-testable rungs.
- **[TASKS.md](TASKS.md)** — beads-style task ledger.

## Steering documents (enforced as review rubrics)
- **[../STYLE.md](../STYLE.md)** — engineering principles + concrete Rust norms.
- **[../PORTING_RULES.md](../PORTING_RULES.md)** — Java→Rust translation rules.
- **[../SEMANTICS_LEDGER.md](../SEMANTICS_LEDGER.md)** — human-owned behavioral rules pinned to Alloy; agents implement from here.
- **[../LIMITATIONS.md](../LIMITATIONS.md)** — honest, current list of what mettle can't do yet.

## Decisions
- **[adr/](adr/)** — Architecture Decision Records. Index: [adr/README.md](adr/README.md).

## Reference material
- **[reference/](reference/)** — verified briefs on the reference implementation (e.g. the pinned Alloy 6 oracle).

## Operating guide
- **[../CLAUDE.md](../CLAUDE.md)** — lean agent operating guide (roles, cadence, delegation, principles). Progressive-disclosure hub.

## Conventions
- **Doc status.** Live-state docs are updated in place. Steering docs carry a `Status: living document` line. ADRs are immutable once `Accepted`; to change a decision, add a new ADR that `Supersedes` the old one and flip the old one's status to `Superseded by ADR-XXXX`.
- **Linking.** Any new doc must be linked from this index (or from a doc that is). If it isn't reachable here, it doesn't exist.
