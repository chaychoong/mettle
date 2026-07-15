# Task ledger (beads)

Lightweight, git-tracked, greppable task "beads" — no external tool dependency (see [ADR-0004](adr/0004-docs-and-task-system.md); we may adopt Steve Yegge's `bd`/beads tool later if the dependency graph warrants it).

**Bead format:** `mt-NNN` id · `status` · `rung/phase` · short title. Detail and dependencies below each. Statuses: `todo` `doing` `blocked` `done`. Reference beads by id from commits and ADRs.

**Legend:** ▢ todo · ◐ doing · ⛔ blocked · ✔ done

---

## Done (Pre-Rung-1)

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

## Done (Rung 1 — syntax) — owner touchpoint passed 2026-07-15
- ✔ **mt-010** · R1 · Lexer + spans (delegated → sonnet, tech-lead reviewed)
  Done 2026-07-15: raw-token lexer per the pinned contract ([reference/alloy6-grammar.md](reference/alloy6-grammar.md) §1, [ADR-0007](adr/0007-rung1-lexer-parser-architecture.md)); typed `LexError` with caret-ready spans; **167/167 corpus files lex clean**. Review caught + jar-verified two divergences (number maximal-run rule: `1_000`/`0x123`/`0b12` illegal; string-follow class includes digits/quotes) — spec §1.5–1.6 corrected to match.
- ✔ **mt-011** · R1 · Parser + arena AST (delegated → opus, tech-lead reviewed)
  Done 2026-07-15: full surface grammar → arena AST; `cook.rs` (F1–F4) + `parser.rs` (recursive descent + Pratt, 21 levels, binder rule, min-BP-gated prefixes). **167/167 corpus parse rate.** Review caught 2 real bugs pre-merge (`;`-grouping semantics; prefix over-acceptance) + approved `Expect::Other(i32)`. Deferred: steps-scope build checks → resolve (LIMITATIONS).
- ✔ **mt-012** · R1 · Pretty-printer + parse→print→parse round-trip (delegated → opus, tech-lead reviewed)
  Done 2026-07-15: minimal-paren precedence-aware printer as `Display` (R9d) sharing one bp table with the parser (new `prec` module — no drift possible); span-free `dump` as round-trip witness; insta snapshots (U2, first dev-dep per P1); **corpus round-trip 167/167** (parse→print→reparse→dump-equal + print idempotence); `mettle parse <file> [--ast]` CLI (hand-rolled args; `file:line:col` errors to stderr per E3) = the Rung-1 human-testable build. Review trims: dropped gratuitous Vec clones, `prec` made pub(crate) (S4). No parser bugs surfaced.
- ✔ **mt-013** · R1 · Diagnostics (caret errors) + Alloy4Fun error-quality pass (delegated → sonnet, tech-lead reviewed)
  Done 2026-07-15: rustc-style caret renderer in `crates/mettle/src/diagnostics.rs` (E3; multi-line/tab/EOF/UTF-8 edge cases unit-tested); alloy4fun differential pass (186k records → 150,891 unique) via new batch `ParseOnlyShim.java`. **2 real parser bugs found+fixed** w/ regression tests (closure-prefix binder exception; bare `disj`/`pred/totalOrder` over-acceptance). Zero jar-accepts+mettle-rejects; 99.79% exact position match; 2/1000 over-acceptance (binder composition) documented in LIMITATIONS → mt-014 bait. Evidence: [reference/alloy4fun-error-pass.md](reference/alloy4fun-error-pass.md).
- ✔ **mt-014** · R1 · Mutation fuzzer + binder-composition resolution (delegated → sonnet, tech-lead reviewed; binder rule independently re-verified against the jar 6/6, fuzzer determinism re-run, grammar-doc §3.1 corrected to the narrowed rule)
  Done 2026-07-15: zero-dep SplitMix64-seeded mutation harness (`tests/fuzz_mutations.rs`: byte/token/splice classes + deep-nesting/long-chain stressors; no-panic + sane-span + round-trip properties; default 4,248 mutants/~5s, `METTLE_FUZZ_ITERS` env override for offline runs, verified at 88,500 mutants/~127s). **Deep-nesting guard required** (measured, not assumed): unguarded `(`/`{`/binder-chain nesting SIGABRTs a debug build well within fuzz reach (worst-case ~212 levels safe on a 1 MiB thread) — `MAX_EXPR_DEPTH = 256` + new `ParseError::TooDeep`, verified safe to 100,000 adversarial levels; jar-probed as a deliberate, better-than-reference divergence. **Part 2 resolved:** ~220 jar probes mapped the exact binder-composition rule (one composition "hop", refreshed by `implies`, hard-blocked by comparisons/set-tests) → shared `crate::prec::child_binder_budget` threaded through both parser (`ParseError::BinderNeedsParens`) and printer (so the two can't drift); LIMITATIONS.md entry resolved. Fuzzer itself found and fixed one real bug (printer under-parenthesizing post-Part-2, since `needs_parens` only tracked `rightmost` not the new budget) and one documented-out-of-scope finding (printer/dumper recursion depth on long flat chains — candidate follow-up bead). 167/167 corpus preserved; full workspace gauntlet green. Evidence: [reference/fuzzing.md](reference/fuzzing.md). **Rung 1 complete → owner touchpoint.**

## Now (Rung 2 — names & types)
Rung gauge: **same accept/reject decisions as the jar** on resolve/typecheck (ROADMAP rung 2). Home crate: `als-types` ("name resolution, sig hierarchy, and the relevance/type checker"). Filed 2026-07-15 after the Rung-1 owner touchpoint.

- ▢ **mt-016** · R2 · Pinned resolution & type-system contract (delegate → opus: foundational, subtle correctness)
  The rung's authority document, same chain as [ADR-0007](adr/0007-rung1-lexer-parser-architecture.md): reference sources at the jar's build commit `794226dd` → jar probes for anything ambiguous → never memory. Study `CompUtil.parseEverything*`/`CompModule.resolveAll` (module graph, `open` + parametric instantiation + aliases, sig/field/fun/pred registration, enum & `seq` desugaring, implicit `this`, private/meta), `Type`/`ExprChoice` (bounding types: union-of-products, arity rules, type-directed overload disambiguation), and the error-vs-warning taxonomy (A4Reporter; "always empty" relevance warnings vs hard errors). Deliverable: `docs/reference/alloy6-resolution.md` pinning exact accept/reject/warn behavior, + ADR-0008 (resolver architecture) drafted for tech-lead review. Blocks mt-017/018.
- ▢ **mt-017** · R2 · Module graph + `open` resolution (`als-types`)
  File loading + search order (model dir, embedded mettle stdlib), parametric module instantiation, `as` aliases + qualified-name tables, duplicate-open dedup and cycle handling — exactly per the mt-016 contract. Lands together with mt-015 (each needs the other to be exercisable). Depends: mt-016.
- ▢ **mt-015** · R2 · Clean-room `util/*` stdlib rewrite ([ADR-0006](adr/0006-licensing-posture.md))
  Write mettle's own `util/{ordering,integer,boolean,...}.als` from documented interfaces + Ledger-pinned behavior; **never** from upstream's text (corpus copies are test inputs only). Lands with mt-017 `open` resolution; `util/ordering`'s analyzer special-casing (exact bounds/symmetry) needs its own Ledger entries. Depends: mt-016 (interfaces enumerated there), mt-017.
- ▢ **mt-018** · R2 · Name resolution + type checker core (`als-types`)
  Scope chain (module → sig/`this` → params/lets/quantifier vars), field resolution with implicit `this` injection, overload candidate collection + type-directed disambiguation, bounding-type computation with arity checks, emptiness/relevance errors and warnings — all per the mt-016 contract, with typed spanned diagnostics (no rendering; E3). Depends: mt-016, mt-017.
- ▢ **mt-019** · R2 · `mettle check` CLI subcommand
  `mettle check <file.als>`: parse + resolve + typecheck, render resolve/type diagnostics through the mt-013 caret renderer, exit codes per `parse` precedent. The Rung-2 human-testable build. Depends: mt-018.
- ▢ **mt-020** · R2 · Differential resolve/typecheck gauge vs the jar
  Extend the batch shim (mt-013 precedent) to report the jar's post-`resolveAll` verdict; run 167-file corpus (must be 100% accept) + the 150,891 unique alloy4fun codes; triage every disagreement; scorecard + LIMITATIONS updated. The rung's exit gauge. Depends: mt-018 (mt-019 helpful, not required).

## Backlog (later rungs)
Tracked at rung granularity in [ROADMAP.md](ROADMAP.md); expanded into beads when a rung becomes "Next".

- ▢ **mt-021** · R? · Printer/dumper recursion-depth safety on pathologically long flat operator chains
  mt-014's second fuzzer finding (see [reference/fuzzing.md](reference/fuzzing.md) §1): `Ast::pretty`/`dump` recurse per operand and can overflow on adversarial flat chains far beyond any real model. Fixing properly touches the public, currently-infallible `pretty`/`pretty_to_string` signatures — needs a small ADR first. Not rung-gating; schedule opportunistically.
