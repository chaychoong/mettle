# Current state

> The live "where are we" doc. Update this at the end of every work chunk. On pickup, read this first.

**Last updated:** 2026-07-15 (fourth session of this date)
**Current rung:** **Rung 1 (syntax) in progress** — mt-010 lexer + mt-011 parser + mt-012 printer + mt-013 diagnostics DONE; mt-014 fuzzer closes the rung (see [ROADMAP.md](ROADMAP.md))
**Conformance scorecard:** harness exists (Net 0 live); mettle-side solving not yet implemented. Rung-1 gauge: **corpus lex, parse, AND round-trip rate 167/167** (alloytools-models + portus-63). Oracle baseline committed: `baselines/` (234 jar verdicts over alloytools-models, triaged).
**Builds:** `cargo build/fmt/clippy/test` all green workspace-wide (~175 tests). **Human-testable now:** `cargo build -p mettle && ./target/debug/mettle parse <file.als>` pretty-prints any Alloy 6 model (`--ast` for the structural dump).

## What exists
- Repo initialized at `~/repos/mettle` (git, not yet published to a remote).
- Documentation spine: `CLAUDE.md`, `docs/` (index, STATE, ROADMAP, TASKS, ADRs 0001–0005), `LIMITATIONS.md`, `SEMANTICS_LEDGER.md`. Session routines: pickup in `CLAUDE.md` → "Start here"; close via `docs/SESSION_WRAP.md`; lessons in `docs/LESSONS.md`.
- **Binding steering rubrics:** `STYLE.md` + `PORTING_RULES.md` (numbered rules D#/I#/E#/R# citable in review).
- **Pinned conformance oracle:** Alloy **6.2.0** (ADR-0002, [reference/alloy6-reference.md](reference/alloy6-reference.md)); jar in git-ignored `oracle/`.
- **Cargo workspace (mt-004):** 8 crates on the hand-designed DAG; CI at `.github/workflows/ci.yml`.
- **Core type skeleton (mt-005, [ADR-0005](adr/0005-core-ir-type-skeleton.md)):** `als-syntax` = `Arena<I,T>`/`ArenaId`/`define_id!` + `Span`/`FileId` + the full Alloy 6 surface AST (unified `Expr`, temporal first-class, spans required); `als-core` = three-sorted relational IR (`Formula`/`RelExpr`/`IntExpr`) + `Universe`/`TupleSet`/`Bounds` (BTree-ordered, invariants asserted); `als-solve` = dependency-free `Var`/`Lit`/`Cnf`/`Assignment`/`Outcome` + `Solver` trait. Bones only — Rung 1+ fills flesh behind these shapes.
- **Conformance harness v0 (mt-006):** `als-conform` drives the jar via `crates/als-conform/shim/OracleShim.java` (`A4Options` API; symmetry/noOverflow/solver always explicit; `noOverflow=true` default per LEDGER-001), per-file JVM with timeout + scratch CWD, typed outcomes (Sat/Unsat/Timeout/Error), Net 0 expect-mining, deterministic text+JSON scorecard. Run it: `cargo build -p als-conform && ./target/debug/conform oracle` (or any `.als` dir; `--symmetry 0 --enumerate exhaustive` = ADR-0002's counting config). 5 jar-integration tests pin the known 87/1129 enumeration facts; they skip cleanly when the jar is absent (CI has no JDK).
- **Corpora vendored locally (mt-007, [reference/corpora.md](reference/corpora.md)):** `corpus/` (git-ignored pending mt-008) holds alloytools-models (94 .als, pinned to the jar's build commit), alloy4fun (Zenodo DOI 10.5281/zenodo.17390557, 186k JSON-Lines records, CC-BY-4.0), portus-63 (63 supported models + deps; licensing hot spot: 2× GPL-3.0, 6× no-license). kodkod: investigated, no `.als` content, not vendored. All retrieval commands recorded verbatim in the manifest — fully reproducible.
- **Pinned syntax contract (mt-010/011 spec, [reference/alloy6-grammar.md](reference/alloy6-grammar.md), [ADR-0007](adr/0007-rung1-lexer-parser-architecture.md)):** token set, filter rewrites F1–F4, 21-level precedence, grammar shapes — derived from the oracle build's grammar sources and jar-verified. AST extended to grammar parity in the same commit.
- **Lexer (mt-010):** `als-syntax::{token,lexer}` — raw spanned tokens, typed `LexError`, 167/167 corpus lex rate (`tests/corpus_lex.rs`, skips without `corpus/`).
- **Parser (mt-011):** `als-syntax::{cook,parser}` — F1–F4 cooking pass + recursive-descent/Pratt parser into the arena AST; typed `ParseError` with the reference's parse-time checks; 167/167 corpus parse rate (`tests/corpus_parse.rs`).
- **Pretty-printer (mt-012):** `als-syntax::print` — minimal-paren precedence-aware `Display` printer + span-free structural `dump` (round-trip witness); `als-syntax::prec` is the single binding-power table shared by parser and printer. 167/167 corpus round-trip (`tests/corpus_roundtrip.rs`: parse→print→reparse→dump-equal + idempotence); insta snapshots (first dev-dep). CLI: `mettle parse <file.als> [--ast]` (canonical source or dump to stdout).
- **Diagnostics + alloy4fun pass (mt-013):** rustc-style caret errors in `crates/mettle/src/diagnostics.rs` (CLI-only per E3); differential parse pass vs. the jar over 150,891 unique alloy4fun codes via batch `crates/als-conform/shim/ParseOnlyShim.java` — zero jar-accepts+mettle-rejects, 99.79% exact error-position match, 2 parser bugs fixed w/ regression tests, 2 narrow divergences documented in LIMITATIONS. Evidence: [reference/alloy4fun-error-pass.md](reference/alloy4fun-error-pass.md).
- **Oracle baseline (`baselines/`):** 234 per-command jar verdicts over alloytools-models at LEDGER-001 defaults, with triage (3 stale upstream expects, 7 genuine engine-limit errors, 1 timeout) — the comparison set once mettle solves.
- Toolchains in this VM: Rust stable (`~/.cargo/bin`) and OpenJDK 21.

## In flight (delegated, background)
- _None._ All delegations complete, reviewed, merged (latest: mt-013 diagnostics).

## Not yet started
- Rung 1 remainder: mutation fuzzer (mt-014) — the last bead before the Rung-1 owner touchpoint.
- Extending the scorecard to run mettle-side once anything parses/solves.

## Next chunk (planned)
**On "proceed", start mt-014: mutation fuzzer over the corpora.** Deterministic (seeded, D4) mutation of corpus + alloy4fun sources — token-level splices, deletions, duplications, truncations, random byte noise — asserting the front end never panics, never loops, and always produces a spanned, typed error or a valid AST; plus a round-trip check on every mutant that still parses (parse→print→reparse→dump-equal, extending mt-012's oracle). Priority target from mt-013: the binder-composition over-acceptance documented in LIMITATIONS (jar-map the exact per-level rule, then decide fix vs. keep-documented, with a Ledger entry if behavior is pinned). After mt-014 lands, **Rung 1 is complete → owner touchpoint** with the `mettle parse` build and one concrete thing to try.

## Key syntax facts pinned this session (details in [reference/alloy6-grammar.md](reference/alloy6-grammar.md))
- The public grammar appendix is NOT the truth; the reference's `Alloy.lex`/`Alloy.cup`/`CompFilter` at the jar's build commit are, plus jar probes for anything ambiguous.
- `Version.experimental = true` is compiled into the pinned jar → string literals and range scopes (`for 1..4 steps`, `3..:2`) are live syntax.
- Number literals: maximal-run rule; `1_000`, `0x123`, `0b12` are syntax errors; `0x_12`, `0b1_0` are fine.
- Five token-stream rewrites sit between lexer and parser (label reorder, not/comparison + fun-op + arrow merges, minus folding, quantifier disambiguation) — spec §2.

## Recent decisions
- **ADR-0007 — Rung-1 front end (2026-07-15):** hand-written lexer + recursive-descent/Pratt parser, zero new runtime deps; F1–F4 token rewrites as a separate cooking pass; fail-fast precise errors for Rung 1 (recovery = mt-013); authority chain grammar-doc → jar → never memory. The public grammar appendix is NOT authoritative — the reference's `Alloy.lex`/`Alloy.cup`/`CompFilter` at the jar's build commit are.
- **AST parity extensions (tech-lead, with mt-011):** `SigParent::Eq`, `Para::Macro`, `ParaName` string names, `is_bound_disj`, scope ranges (`ScopeEnd`, increments, Steps/Str targets), `Expect::Other(i32)`, `UnOp::{ExactlyOf,IntOf,SumOf}`, integer `fun/` BinOps; builtin keyword-names (`Int`, `disj`, `fun/min`…) are synthesized `Name`s resolution keys on.
- **ADR-0006 — licensing (mt-008, owner-decided 2026-07-15):** mettle = **MPL-2.0** (root LICENSE, workspace manifest); `util/*.als` stdlib = **clean-room rewrite** (bead mt-015 — never copy upstream text; corpus copies are test inputs only); corpora local-only forever; PORTING_RULES legal-hygiene updated accordingly.
- **ADR-0005** — core IR type skeleton: shared arena/ID infra in `als-syntax`; unified surface `Expr` vs three-sorted IR; BTree-ordered bounds; dependency-free `als-solve`; overflow semantics live in the translator, not the types.
- **LEDGER-001 — overflow default = FORBID** (approved 2026-07-15). Harness already sets the oracle to match (`no_overflow=true` default, `--allow-overflow` to flip).
- Shim source lives **inside the crate** (`crates/als-conform/shim/`), not git-ignored `oracle/` — our own code must survive a fresh clone; only the re-downloadable jar stays ignored.

## Open questions for the human (non-blocking)
- _None._ (mt-008 licensing resolved via ADR-0006; next owner touchpoint is the Rung-1 build to try.)
