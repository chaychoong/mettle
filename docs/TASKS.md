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
- ✔ **mt-006** · P0 · Conformance harness (`als-conform`) v0 (delegated → sonnet, tech-lead reviewed)
  Done 2026-07-15: `crates/als-conform/shim/OracleShim.java` drives the jar via the `A4Options` API (symmetry/noOverflow/solver always explicit; LEDGER-001 default); Rust side = typed outcomes, timeout-killed JVM per file, Net 0 expect-mining, deterministic scorecard (text+JSON), `conform` bin. 87/1129 enumeration facts pinned by integration tests (skip cleanly sans jar). Review fixes: shim source moved into the crate (was in git-ignored `oracle/`); unknown solver = hard error, no silent default.
- ✔ **mt-007** · P0 · Vendor corpora (delegated → sonnet, tech-lead reviewed)
  Done 2026-07-15: alloytools-models (94 .als @ the jar's build commit), alloy4fun (Zenodo 10.5281/zenodo.17390557, CC-BY-4.0), portus-63 (63 models, licensing hot spot) vendored into git-ignored `corpus/`; kodkod investigated → no `.als`, not vendored. Provenance manifest committed: [reference/corpora.md](reference/corpora.md). Corpus files stay uncommitted until mt-008.
- ▢ **mt-008** · P0 · Resolve licensing posture (ADR)
  Upstream Alloy's own license is unsettled (repo `LICENSE` says "NOT VALID YET / currently MIT"; per-file headers + jar manifest say MIT; bundled `LICENSE.txt` is Apache-2.0). Kodkod=MIT, SAT4J=LGPL-2.1 (oracle-only, not shipped in product). `util/*.als` carry **no** license header. Decide mettle's own license + attribution/NOTICE and how to vendor `util/*.als`; write a licensing ADR. See reference doc §2. *Blocks shipping any vendored corpus/stdlib.*

## Next (Rung 1 — syntax)
- ▢ **mt-010** · R1 · Lexer + spans (temporal tokens included) ← **next on "proceed"** (with mt-011; AST contract = `als-syntax::ast`, ADR-0005)
- ▢ **mt-011** · R1 · Parser + arena AST (temporal syntax included)
- ▢ **mt-012** · R1 · Pretty-printer + parse→print→parse round-trip
- ▢ **mt-013** · R1 · Diagnostics (caret errors) + Alloy4Fun error-quality pass
- ▢ **mt-014** · R1 · Mutation fuzzer over corpora (parser robustness)

## Backlog (later rungs)
Tracked at rung granularity in [ROADMAP.md](ROADMAP.md); expanded into beads when a rung becomes "Next".
