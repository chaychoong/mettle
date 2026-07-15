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
- ✔ **mt-008** · P0 · Resolve licensing posture (ADR)
  Done 2026-07-15, owner-decided → [ADR-0006](adr/0006-licensing-posture.md): mettle = **MPL-2.0** (root LICENSE + workspace manifest); stdlib `util/*.als` = **clean-room rewrite** (bead mt-015, never copy upstream text); corpora = local-only forever (git-ignored, reproducible via manifest + mt-009 script); jar stays ignored. PORTING_RULES legal-hygiene section updated per the ADR.
- ✔ **mt-009** · P0 · Reproducible corpus fetch script (delegated → sonnet, tech-lead reviewed)
  Done 2026-07-15: `scripts/fetch-corpora.sh` (+ `corpora.sha256`, 192 files) reproduces `corpus/` byte-identically from the [reference/corpora.md](reference/corpora.md) pins in ~15s (alloy4fun optional via `--with-alloy4fun`); `--verify` re-checked independently: 192/192 pass, shellcheck clean. Bonus: surfaced and fixed an under-documented 4th upstream patch (`trace.als`) — manifest corrected.

## Next (Rung 1 — syntax)
- ◐ **mt-010** · R1 · Lexer + spans (temporal tokens included)
  Contract pinned in [reference/alloy6-grammar.md](reference/alloy6-grammar.md) + [ADR-0007](adr/0007-rung1-lexer-parser-architecture.md); AST extended to grammar parity (SigParent::Eq, macros, ParaName, scope ranges, int ops, ExactlyOf). Implementation delegated (sonnet); gauge = 100% corpus lex rate.
- ◐ **mt-011** · R1 · Parser + arena AST (temporal syntax included)
  Same contract; recursive descent + Pratt over the 21-level table, filter rewrites F1–F4 as parser lookahead/cooking pass. Delegated (opus) after mt-010 merges; gauge = corpus parse rate.
- ▢ **mt-012** · R1 · Pretty-printer + parse→print→parse round-trip
- ▢ **mt-013** · R1 · Diagnostics (caret errors) + Alloy4Fun error-quality pass
- ▢ **mt-014** · R1 · Mutation fuzzer over corpora (parser robustness)

## Backlog (later rungs)
Tracked at rung granularity in [ROADMAP.md](ROADMAP.md); expanded into beads when a rung becomes "Next".

- ▢ **mt-015** · R2 · Clean-room `util/*` stdlib rewrite ([ADR-0006](adr/0006-licensing-posture.md))
  Write mettle's own `util/{ordering,integer,boolean,...}.als` from documented interfaces + Ledger-pinned behavior; **never** from upstream's text (corpus copies are test inputs only). Lands with Rung-2 `open` resolution; `util/ordering`'s analyzer special-casing (exact bounds/symmetry) needs its own Ledger entries.
