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
  - **[reference/alloy4fun-resolve-pass.md](reference/alloy4fun-resolve-pass.md)** — the differential resolve/typecheck gauge (mt-020, tightened by mt-022 §9 and mt-025 §10) over the 150,891-unique-code alloy4fun corpus + the 167-file corpus against the reference jar: harness, per-bead before/after, final numbers (0 drop-in violations both directions, 167/167 corpus, 99.79% alloy4fun agreement), and the root-caused residual.
  - **[reference/warning-parity.md](reference/warning-parity.md)** — mt-023's warning-set differential (the LEDGER-002 owner requirement): the full §5.2 catalog implementation, the jar-stem→class table, parity numbers (99.80% files identical, 0 missing on corpus, 98.6% recall on alloy4fun), and the root-caused remainder in both directions.
  - **[reference/alloy6-translation.md](reference/alloy6-translation.md)** — the pinned Alloy 6 translation & solving contract that Rung 3 (mt-028, §1–§10) and Rung 4 (mt-043, §11–§16) implement: scopes→universe→bounds (exact atom naming/order), resolved-Expr→relational mapping, skolemization, symmetry breaking, SAT boundary, outcome/enumeration semantics, `util/ordering` special-casing (→ LEDGER-004), **integer arithmetic at bitwidth + the Milicevic/Jackson overflow-polarity rule, the `Int/min|max|next|zero` builtins, String atom minting, `seq` semantics, first-order skolemization, and the SB-20 posture (→ LEDGER-005/006/007/008, ADR-0012)**, and the jar-probe log (incl. the `expect 1` ⇒ `symmetry 0` gotcha).
- **[../baselines/](../baselines/README.md)** — cached reference-jar verdicts over the corpora (the answers mettle must match), with triage notes on expect-mismatches and engine-limitation errors.

## Operating guide
- **[../CLAUDE.md](../CLAUDE.md)** — lean agent operating guide (roles, cadence, delegation, principles). Progressive-disclosure hub.

## Conventions
- **Doc status.** Live-state docs are updated in place. Steering docs carry a `Status: living document` line. ADRs are immutable once `Accepted`; to change a decision, add a new ADR that `Supersedes` the old one and flip the old one's status to `Superseded by ADR-XXXX`.
- **Linking.** Any new doc must be linked from this index (or from a doc that is). If it isn't reachable here, it doesn't exist.
