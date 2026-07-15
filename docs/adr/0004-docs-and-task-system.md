# ADR-0004 — Documentation & task-tracking system

**Status:** Accepted
**Date:** 2026-07-15

## Context
The project is built primarily by an agent fleet across many sessions under human review. Smooth cross-session handoff, referenceable decisions, and a lean-but-complete knowledge base are load-bearing, not nice-to-haves. The product owner asked for: live "current state" docs, ADRs, everything cross-linked (nothing orphaned), a lean progressively-disclosed `CLAUDE.md`, and a todo system ("a list, or Yegge's beads").

## Decision
- **Live-state docs** in `docs/`: `STATE.md` (updated every chunk, the pickup point), `ROADMAP.md`, `TASKS.md`. Updated in place.
- **ADRs** in `docs/adr/`, immutable once Accepted; superseded by adding a new ADR, never edited away.
- **Everything is reachable from [docs/README.md](../README.md).** A doc that isn't linked there (or from something linked there) does not exist. Superseded docs are marked, not deleted.
- **`CLAUDE.md` stays lean** via progressive disclosure — it links to the docs rather than duplicating them, and is updated whenever the operating model changes.
- **Task tracking = a git-tracked, greppable markdown "beads" ledger** (`docs/TASKS.md`) with stable ids (`mt-NNN`), statuses, and dependencies. **No external tool dependency now** (honors "no unnecessary tech debt"). We may adopt Steve Yegge's `bd`/beads tool later *iff* the dependency graph grows complex enough to justify a dependency; that would be a new ADR.
- **The harness `TaskCreate`/todo tools are for within-session scratch only**; durable cross-session tasks live in `docs/TASKS.md`.

## Consequences
- Every session starts by reading `docs/STATE.md`; every chunk ends by updating it.
- Commit messages and ADRs reference beads by id (`mt-NNN`) for traceability.

## Alternatives considered
Adopting `bd`/beads immediately (deferred: premature dependency). Tracking tasks only in the ephemeral harness todo tool (rejected: doesn't survive sessions / isn't referenceable).
