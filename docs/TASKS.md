# Task ledger (beads)

Lightweight, git-tracked, greppable task "beads" — no external tool dependency (see [ADR-0004](adr/0004-docs-and-task-system.md); we may adopt Steve Yegge's `bd`/beads tool later if the dependency graph warrants it).

**Bead format:** `mt-NNN` id · `status` · `rung/phase` · short title. Detail and dependencies below each. Statuses: `todo` `doing` `blocked` `done`. Reference beads by id from commits and ADRs.

**Legend:** ▢ todo · ◐ doing · ⛔ blocked · ✔ done

---

## Now (Pre-Rung-1)

- ✔ **mt-001** · P0 · Documentation & decision spine
  CLAUDE.md, docs index, STATE, ROADMAP, this ledger, ADRs 0001–0004, LIMITATIONS, Ledger scaffold.
- ✔ **mt-002** · P0 · Pin the conformance oracle (delegated → sonnet)
  Downloaded + verified Alloy 6.2.0 jar (SHA-256 pinned); proved headless verdict/count/`symmetryBreaking=0`/overflow-default/SAT4J, and found+documented a CLI bug (`-y`/`--ymmetry` is a no-op — use the `A4Options` API instead). → `docs/reference/alloy6-reference.md`; SHA/version folded into ADR-0002.
- ✔ **mt-003** · P0 · Draft steering rubrics (delegated → opus)
  STYLE.md + PORTING_RULES.md — tech-lead reviewed and accepted as binding rubrics.
- ✔ **mt-004** · P0 · Cargo workspace + `als-*` crate skeleton (delegated → sonnet)
  8 crates on the hand-designed DAG; binary crate = package `mettle` (fulfils the plan's `als-cli` role). CI green (build/fmt/clippy -D warnings/test), tech-lead re-verified. `Cargo.lock` committed.
- ✔ **mt-005** · P0 · Hand-designed core IR type skeleton (tech-lead-authored, NOT delegated)
  Done 2026-07-15: `Arena`/`ArenaId`/`define_id!` + `Span` in als-syntax; unified surface AST (temporal-first, spans required); three-sorted relational IR + `Universe`/`TupleSet`/`Bounds` in als-core; dependency-free `Var`/`Lit`/`Cnf`/`Solver` boundary in als-solve. Rationale: [ADR-0005](adr/0005-core-ir-type-skeleton.md).
- ◐ **mt-006** · P0 · Conformance harness (`als-conform`) v0 (delegated → sonnet, in flight)
  Drive the pinned jar; produce a scorecard artifact. Cross-check against `expect` annotations (Net 0). **Drive via a compiled `A4Options` Java shim (see `oracle/Harness.java`), NOT `exec -y` (that CLI flag is a confirmed no-op in 6.2.0); force `-s sat4j` for zero native deps; run in a temp workdir (exec litters an output dir named after the model into CWD).** Depends on mt-002, mt-004.
- ◐ **mt-007** · P0 · Vendor corpora (delegated → sonnet, in flight)
  AlloyTools examples, Alloy4Fun/NoviceAlloyModels, Portus 63, Kodkod tests — with licenses/headers. Depends on mt-002. **Scope note (mt-008 gate):** downloads land in git-ignored `corpus/`; only the provenance manifest (`docs/reference/corpora.md`) + `.gitignore` are committed until licensing resolves.
- ▢ **mt-008** · P0 · Resolve licensing posture (ADR)
  Upstream Alloy's own license is unsettled (repo `LICENSE` says "NOT VALID YET / currently MIT"; per-file headers + jar manifest say MIT; bundled `LICENSE.txt` is Apache-2.0). Kodkod=MIT, SAT4J=LGPL-2.1 (oracle-only, not shipped in product). `util/*.als` carry **no** license header. Decide mettle's own license + attribution/NOTICE and how to vendor `util/*.als`; write a licensing ADR. See reference doc §2. *Blocks shipping any vendored corpus/stdlib.*

## Next (Rung 1 — syntax)
- ▢ **mt-010** · R1 · Lexer + spans (temporal tokens included)
- ▢ **mt-011** · R1 · Parser + arena AST (temporal syntax included)
- ▢ **mt-012** · R1 · Pretty-printer + parse→print→parse round-trip
- ▢ **mt-013** · R1 · Diagnostics (caret errors) + Alloy4Fun error-quality pass
- ▢ **mt-014** · R1 · Mutation fuzzer over corpora (parser robustness)

## Backlog (later rungs)
Tracked at rung granularity in [ROADMAP.md](ROADMAP.md); expanded into beads when a rung becomes "Next".
