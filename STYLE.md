# STYLE.md — mettle Rust engineering rubric

Purpose: the enforced code-review rubric for all mettle Rust. Every PR is judged against these bullets; cite them by number in review.

Status: living document (see "Proposing changes" at the end).

Correctness over everything. Do not take on unnecessary tech debt. Write idiomatic Rust. When a rule and a shortcut conflict, the rule wins.

---

## 1. Determinism (non-negotiable)

- D1. Same input + same scopes -> byte-identical output and identical instance-enumeration order, on every machine and every run, **for a fixed solver build**. Determinism means self-consistency, NOT matching the reference jar's CNF or ordering.
- D2. No `HashMap`/`HashSet` iteration anywhere that can influence variable numbering, CNF emission, or any user-visible output. Use `IndexMap`/`IndexSet` (insertion order) or `BTreeMap`/`BTreeSet` (key order), or collect and `sort`/`sort_by_key` before iterating.
- D3. `HashMap`/`HashSet` are allowed ONLY as internal lookup caches whose iteration order never escapes (membership/get only). If in doubt, use `IndexMap`.
- D4. No wall-clock, no thread scheduling, no address/pointer values, and no unseeded randomness in the pipeline. Any randomness is explicitly seeded and the seed is part of the recorded input.
- D5. Parallelism must not affect results: reduce/merge in a fixed order, never in completion order.

## 2. Assert invariants, including negative space

- I1. State invariants as `assert!`/`debug_assert!` at the boundary that establishes them: arities agree through every operation; matrices stay consistent with their bounds; variable numbering is dense (no gaps).
- I2. Debug builds re-check the decoder: decoded instance re-satisfies the emitted formula (`debug_assert!`), so a wrong solution fails loudly in CI.
- I3. Cases unreachable by construction use `unreachable!()`/`debug_assert!(false, ...)` with a one-line reason — never a silent `// can't happen` comment or a fake fallback value.
- I4. Assertion messages name the invariant, not the symptom (e.g. `"arity mismatch: lhs={l} rhs={r}"`).
- I5. Assertions guard internal invariants only. Never assert on user input (see §3).

## 3. Error handling

- E1. Libraries return `Result<T, E>` with typed errors (`thiserror`-style enums). One error enum per crate/phase; variants carry span + context, not just strings.
- E2. `panic!`/`unwrap`/`expect`/`unreachable!` are for genuine internal invariant violations ONLY. Never on user input, I/O, or any recoverable condition.
- E3. The CLI crate is the ONLY place that turns `Result`/error enums into human diagnostics. Library crates never print, never `eprintln!`, never `std::process::exit`.
- E4. Prefer `?` and `map_err` over match-and-rewrap. Do not stringify errors early (no `.map_err(|e| e.to_string())` inside libs) — keep them typed until the CLI.
- E5. Unsupported-but-parsed features return a precise typed error ("parsed, not yet solvable: <feature> at <span>"), never a wrong answer and never a generic panic. See §11.

## 4. Function, module, and file size

- S1. Single responsibility: a function does one nameable thing. If the doc-comment needs "and", split it.
- S2. Soft caps: functions ~60 lines, files ~500 lines. Over cap is allowed only with a one-line justification comment; use it as a smell, not a hard gate.
- S3. Modules mirror pipeline phases (lexer, parser, ast, resolve, ir, translate, solve, decode, diagnostics). Cross-phase helpers live in a shared crate, not smeared across phases.
- S4. Keep `pub` surface minimal; default to private, promote deliberately.

## 5. Naming conventions

- N1. Types/traits/enums/variants: `UpperCamelCase`. Functions/methods/vars/modules: `snake_case`. Consts/statics: `SCREAMING_SNAKE_CASE`.
- N2. Typed arena IDs are newtypes ending in `Id`: `NodeId`, `SigId`, `VarId`, `RelId`. Never pass a bare `usize`/`u32` as an index across an API.
- N3. Arena fields/locals are plural or `_arena`: `nodes`, `sigs`, `node_arena`. An arena and its ID type share a stem (`Sig`/`SigId`/`sigs`).
- N4. No Hungarian, no `_impl`/`_helper` suffixes as a substitute for a real name. No abbreviations that aren't domain terms (`sig`, `rel`, `cnf` are fine).
- N5. Predicates read as questions: `is_temporal`, `has_prime`.

## 6. Arena discipline

- A1. ASTs/IRs are index-based: `Vec<T>` arenas + typed `Id` newtypes (rustc-style). No `Rc<RefCell<...>>` object graphs, no back-pointers-by-reference.
- A2. Each phase owns its arenas; allocation is a visible phase-boundary act (a phase takes input arenas, produces new ones). No hidden global growth.
- A3. Bidirectional/child->parent links are stored as `Id`s, resolved through the owning arena, not as Rust references.
- A4. IDs are only valid within their owning arena; never mix IDs from different arenas. Encode the arena in the type where feasible.

## 7. Collections in hot / numbering / output paths — FORBIDDEN

- C1. In any path touching variable numbering, CNF emission, enumeration order, or output: no dependence on `HashMap`/`HashSet` iteration order (restates D2 as a review gate).
- C2. Required substitutes: `IndexMap`/`IndexSet`, `BTreeMap`/`BTreeSet`, or `Vec` + explicit sort. Reviewer must be able to point at the ordering guarantee.
- C3. New dependency on any such collection type must cite which guarantee (insertion vs key order) the code relies on.

## 8. Dependencies

- P1. Every dependency is justified in writing (one line in the PR and in `Cargo.toml` comment): what it does, why not std, why this crate.
- P2. Small tree, single static binary. Prefer std; prefer one well-known crate over several overlapping ones.
- P3. Pure-Rust SAT first — **zero FFI in v1**. FFI solvers arrive later behind a `Solver` trait; no FFI leaks into core crates.
- P4. No dep pulls in async runtimes, C toolchains, or proc-macro-heavy trees without explicit lead sign-off.

## 9. Spans & diagnostics

- G1. Every AST node carries a source `Span` from day one; constructing a node without a span is a compile error (span is a required field, not `Option`).
- G2. Spans propagate through resolve/IR so diagnostics point at original source, not desugared forms.
- G3. Diagnostics are a headline feature: typed errors carry enough span/context for a caret-and-label render in the CLI.

## 10. Formatting & linting

- L1. `cargo fmt` clean; CI fails on diff. No manual alignment that fmt would undo.
- L2. `cargo clippy` clean. Workspace denies: `clippy::all` and `clippy::pedantic` (opt out per-line with a justified `#[allow(...)]` + reason).
- L3. Library crates deny `clippy::unwrap_used` and `clippy::expect_used`; genuine-invariant exceptions use `#[allow(..)]` with a reason naming the invariant. The CLI crate may relax this at its top-level entry only.
- L4. Deny `unsafe` workspace-wide in v1 (`#![forbid(unsafe_code)]`); lifting it anywhere needs lead sign-off (ties to P3, zero-FFI).
- L5. Warnings are errors in CI (`-D warnings`).

## 11. Temporal & unsupported features

- T1. Temporal syntax (variable sigs, primes, `always`/`eventually`) parses from day one — the parser and AST support it even before the solver does.
- T2. Reaching an unsupported-but-valid construct fails LOUDLY and precisely via a typed error (§E5): "parsed, not yet solvable". Never silently ignore, never approximate, never wrong.

## 12. Semantics faithful, structure idiomatic

- M1. Do NOT port Java structure to pin behavior. Pin Java-observable behavior via the conformance suite + Semantics Ledger.
- M2. Workflow: read Java until the behavior can be stated in ONE sentence -> record it in the Semantics Ledger with a test -> implement idiomatically. No "port now, understand later".
- M3. See `PORTING_RULES.md` for Java->Rust translation rules and legal hygiene.

## 13. Testing norms

- U1. Unit tests colocated in `#[cfg(test)] mod tests` next to the code they exercise.
- U2. AST and pretty-printer output use `insta` snapshots; snapshot review is part of PR review. No hand-written giant `assert_eq!` string blobs.
- U3. Every conformance disagreement with the reference becomes a committed regression test the moment it's understood, referencing its Semantics Ledger entry.
- U4. Determinism has a test: run the pipeline twice (and, where cheap, in a fresh process) and assert byte-identical output + identical enumeration order.
- U5. Tests are deterministic too — no timing, no ordering-by-hashmap, no network.

## 14. Comments

- Y1. Comments explain WHY and state invariants; they never restate what the code plainly does.
- Y2. Match surrounding comment density — don't over- or under-annotate relative to the module.
- Y3. Every `unsafe` (if ever permitted), every non-obvious `#[allow]`, and every ordering-critical step carries a one-line rationale.
- Y4. `TODO`/`FIXME` carry an owner or issue reference, or they don't merge.

---

## Proposing changes

This rubric is enforced, not advisory. Agents follow it; they do not reshape it unilaterally. To change a rule: open a brief human-approved note (ADR under `docs/adr/`) stating the rule touched, the rationale, and the migration impact. Reference the ADR in the PR that edits this file. Until an ADR lands, the current text governs review.
