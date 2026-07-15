# Task ledger (beads)

Lightweight, git-tracked, greppable task "beads" — no external tool dependency (see [ADR-0004](adr/0004-docs-and-task-system.md); we may adopt Steve Yegge's `bd`/beads tool later if the dependency graph warrants it).

**Bead format:** `mt-NNN` id · `status` · `rung/phase` · short title. Detail and dependencies below each. Statuses: `todo` `doing` `blocked` `done`. Reference beads by id from commits and ADRs.

**Legend:** ▢ todo · ◐ doing · ⛔ blocked · ✔ done

---

## Now (Pre-Rung-1)

- ✔ **mt-001** · P0 · Documentation & decision spine
  CLAUDE.md, docs index, STATE, ROADMAP, this ledger, ADRs 0001–0004, LIMITATIONS, Ledger scaffold.
- ◐ **mt-002** · P0 · Pin the conformance oracle (delegated → sonnet)
  Download + verify latest Alloy 6 jar; prove headless verdict/count/`symmetryBreaking=0`/overflow-default/SAT4J. → `docs/reference/alloy6-reference.md`; fold SHA/version into ADR-0002. *(agent running)*
- ✔ **mt-003** · P0 · Draft steering rubrics (delegated → opus)
  STYLE.md + PORTING_RULES.md — tech-lead reviewed and accepted as binding rubrics.
- ▢ **mt-004** · P0 · Cargo workspace + `als-*` crate skeleton
  Empty crates per the DAG (plan §3); CI green (fmt + clippy). Depends on mt-003.
- ▢ **mt-005** · P0 · Hand-designed core IR type skeleton
  Typed-index arena IDs + core relational IR types (bones only; agents fill flesh). Depends on mt-004.
- ▢ **mt-006** · P0 · Conformance harness (`als-conform`) v0
  Drive the pinned jar; produce a scorecard artifact. Cross-check against `expect` annotations (Net 0). Depends on mt-002, mt-004.
- ▢ **mt-007** · P0 · Vendor corpora
  AlloyTools examples, Alloy4Fun/NoviceAlloyModels, Portus 63, Kodkod tests — with licenses/headers. Depends on mt-002.

## Next (Rung 1 — syntax)
- ▢ **mt-010** · R1 · Lexer + spans (temporal tokens included)
- ▢ **mt-011** · R1 · Parser + arena AST (temporal syntax included)
- ▢ **mt-012** · R1 · Pretty-printer + parse→print→parse round-trip
- ▢ **mt-013** · R1 · Diagnostics (caret errors) + Alloy4Fun error-quality pass
- ▢ **mt-014** · R1 · Mutation fuzzer over corpora (parser robustness)

## Backlog (later rungs)
Tracked at rung granularity in [ROADMAP.md](ROADMAP.md); expanded into beads when a rung becomes "Next".
