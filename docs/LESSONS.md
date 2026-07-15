# Lessons

Cross-cutting lessons from building mettle — the ones without a more specific home. When a lesson belongs in a rubric (STYLE / PORTING_RULES), a decision ([ADR](adr/)), or a reference gotcha ([reference/](reference/)), put it **there** and just cross-link from here. Filed as part of the [session wrap routine](SESSION_WRAP.md).

## Process / working model
- **Delegate volume, verify the consequential claims yourself.** Background sub-agents carried real load well (`sonnet` for verify-heavy research, `opus` for taste-heavy docs). But the tech lead re-ran the single most verdict-affecting agent finding by hand (the integer-overflow default) instead of trusting the summary — and it mattered. Independently re-verify anything that changes a verdict. → [CLAUDE.md](../CLAUDE.md) Delegation policy.
- **Cold-test the handoff.** A fresh-context, read-only agent given only the repo + "proceed" is a cheap, honest test of whether the docs actually carry the next session. It caught an uncommitted-instruction gap we'd otherwise have shipped. → [SESSION_WRAP.md](SESSION_WRAP.md) §5.
- **Two entry points, one destination.** A session started in `~/repos/mettle` auto-loads the repo `CLAUDE.md`; one started in the website dir auto-loads the cross-session memory instead. Both must funnel to `docs/STATE.md`. Keep both current.

## Reference / oracle gotchas (summary; full detail in [reference/alloy6-reference.md](reference/alloy6-reference.md))
- Alloy 6.2.0's integer-overflow default **differs by entry point** (GUI forbids, headless allows). Never assume a default — set it explicitly. → [LEDGER-001](../SEMANTICS_LEDGER.md).
- The `exec -y/--ymmetry` CLI flag is a **no-op** (upstream aliasing bug); set `symmetryBreaking` via the `A4Options` Java API instead. → bead mt-006.
- `exec` litters an output directory named after the model into the CWD; run the harness in a temp workdir and force `-s sat4j` for zero native deps. → bead mt-006.
