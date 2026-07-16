# mettle documentation index

Every doc in the project is reachable from here. Nothing is orphaned. Superseded docs are marked, not deleted.

## Live state (always current)
- **[STATE.md](STATE.md)** — where we are right now; read this first on pickup.
- **[ROADMAP.md](ROADMAP.md)** — the North Star and the human-testable rungs.
- **[TASKS.md](TASKS.md)** — beads-style task ledger.

## Session routines
- Pickup: **[../CLAUDE.md](../CLAUDE.md)** → "Start here" (what "proceed" means).
- Wrap-up: **[SESSION_WRAP.md](SESSION_WRAP.md)** — the end-of-session checklist.
- **[LESSONS.md](LESSONS.md)** — cross-cutting lessons learned.

## Steering documents (enforced as review rubrics)
- **[../STYLE.md](../STYLE.md)** — engineering principles + concrete Rust norms.
- **[../PORTING_RULES.md](../PORTING_RULES.md)** — Java→Rust translation rules.
- **[../SEMANTICS_LEDGER.md](../SEMANTICS_LEDGER.md)** — human-owned behavioral rules pinned to Alloy; agents implement from here.
- **[../LIMITATIONS.md](../LIMITATIONS.md)** — honest, current list of what mettle can't do yet.

## Decisions
- **[adr/](adr/)** — Architecture Decision Records. Index: [adr/README.md](adr/README.md).

## Reference material
- **[reference/](reference/)** — verified briefs on the reference implementation:
  - **[reference/alloy6-reference.md](reference/alloy6-reference.md)** — the pinned Alloy 6.2.0 oracle: provenance, licenses, and empirically-proven headless invocation.
  - **[reference/corpora.md](reference/corpora.md)** — conformance-corpus provenance manifest: exact pins, retrieval commands, license evidence per corpus (`corpus/` itself is git-ignored pending mt-008).
  - **[reference/alloy6-grammar.md](reference/alloy6-grammar.md)** — the pinned Alloy 6 surface-syntax contract (tokens, filter rewrites, 21-level precedence, grammar shapes) that mt-010/mt-011 implement; derived from the oracle build's grammar sources and jar-verified.
  - **[reference/alloy4fun-error-pass.md](reference/alloy4fun-error-pass.md)** — mt-013's differential parse pass over the 150k-unique-code alloy4fun corpus against the reference jar: methodology, the divergence table, fixes shipped, and what's documented-not-fixed.
  - **[reference/fuzzing.md](reference/fuzzing.md)** — mt-014's mutation fuzzer over the front end (design, budgets, seeds, bugs found) and the jar-mapped binder-composition-budget rule (probe table + fix) that resolves the mt-013 over-acceptance finding.
  - **[reference/alloy6-resolution.md](reference/alloy6-resolution.md)** — the pinned Alloy 6 name-resolution & type-checking contract (mt-016) that Rung 2 implements: `resolveAll` phase pipeline, module system, type system, overload disambiguation, the exact reject/warn taxonomy, `util/*` interfaces (clean-room, signatures only), and the 48-probe jar-verification log.
  - **[reference/alloy4fun-resolve-pass.md](reference/alloy4fun-resolve-pass.md)** — mt-020's differential resolve/typecheck gauge (Rung 2's exit) over the 150,891-unique-code alloy4fun corpus + the 167-file corpus against the reference jar: harness, final numbers (0 drop-in violations, 167/167 corpus, 95.82% alloy4fun agreement), the fixes shipped, and the ADR-0009 decision-3 verdict (measured: leave the accept-lean posture — the tightening needs precise types).
- **[../baselines/](../baselines/README.md)** — cached reference-jar verdicts over the corpora (the answers mettle must match), with triage notes on expect-mismatches and engine-limitation errors.

## Operating guide
- **[../CLAUDE.md](../CLAUDE.md)** — lean agent operating guide (roles, cadence, delegation, principles). Progressive-disclosure hub.

## Conventions
- **Doc status.** Live-state docs are updated in place. Steering docs carry a `Status: living document` line. ADRs are immutable once `Accepted`; to change a decision, add a new ADR that `Supersedes` the old one and flip the old one's status to `Superseded by ADR-XXXX`.
- **Linking.** Any new doc must be linked from this index (or from a doc that is). If it isn't reachable here, it doesn't exist.
