# mt-014 — Mutation fuzzer & binder-composition rule

Evidence doc for bead **mt-014**: (1) a deterministic mutation fuzzer over
the front end, closing out Rung 1's robustness gauge, and (2) the empirical
jar-mapping and fix for the binder-composition over-acceptance LIMITATIONS.md
flagged from mt-013. Kept factual per the bead brief — this is the
referenceable evidence, not a narrative.

## 1. Mutation fuzzer

### Design

`crates/als-syntax/tests/fuzz_mutations.rs` — zero new dependencies (STYLE
P1/P2): a hand-rolled SplitMix64 PRNG (~15 lines, doc-commented) drives every
mutation choice. Mirrors the existing `corpus_lex.rs`/`corpus_parse.rs`/
`corpus_roundtrip.rs` pattern: skips the vendored corpora cleanly (with a
note, not a failure) when `corpus/` is absent, and additionally carries **10
committed inline seed snippets** (sigs, facts, preds/funs, quantifiers/
comprehensions, temporal operators, scopes, `open`) so the test mutates
something meaningful even on a fresh checkout.

**Determinism (STYLE D4).** A named base seed constant (`FUZZ_BASE_SEED`) is
mixed with the seed file's index and the mutation iteration number
(`seed_for`), so two runs over the same corpus produce byte-identical
mutants and identical results — verified by running the test twice in a row
with identical output.

**Mutation classes**, cycled deterministically per iteration so every class
is exercised for every seed file regardless of budget:

- **Byte-level:** truncation at a random point; random single-byte
  flip/insert/delete; **splice** of a random region from a *different*,
  deterministically-chosen seed file into a random position (the classic
  fuzzer "combine two inputs" mutation, not just perturb one).
- **Token-level:** lexes the *original* source, then deletes/duplicates/
  swaps two token spans' raw source text, or moves one token's raw text to a
  different position (`token_reorder`) — always splicing **raw text by
  span**, never re-rendering from token kinds, so every mutant is a genuine
  substring shuffle of real source.
- **Targeted stressors** (a separate, small, fixed set — not randomized):
  deep-nesting probes (`(`, `{`, `~`, `all x: A |` prefixes at depths
  10/100/1,000/10,000) and pathological repetition (long flat `+`/`and`/`.`
  chains at 100/1,000/10,000 terms).

**UTF-8.** Byte-level mutations can produce invalid UTF-8; `parse` takes
`&str`, so every mutant is sanitized with `String::from_utf8_lossy` before
parsing — **lossy, never skipped** (exercises the replacement-character path
through the lexer, which skipping would never reach).

**Properties asserted per mutant:**
1. `parse` returns `Ok` or `Err` — never panics (a genuine panic fails the
   test with the base seed, file, iteration, and a written repro file — see
   below; no `catch_unwind` needed since a failed assertion or a crash both
   already carry that context).
2. On `Err`: `span.start <= span.end`, `span.end <= mutant.len()`, both
   offsets land on a UTF-8 char boundary.
3. On `Ok`: parse → pretty-print → re-parse → dump-equal → idempotent
   re-print (the mt-012 round-trip oracle, reused verbatim).

**Reproducing a failure:** every mutant is written to
`<TMPDIR>/mettle-fuzz-mutant-<seed:016x>.als` *before* it is parsed, and
every assertion message includes the base seed, seed file label, iteration,
mutation kind, and that path — so a failure names an exact byte-for-byte
reproduction, no extra bookkeeping needed.

### Budget

Default `ITERS_PER_SEED_DEFAULT = 24` (per seed file); with the 10 inline
snippets plus the full ~167-file vendored corpus (177 seed files total),
that is **4,248 mutants in ~5.2s** on this machine — comfortably inside the
bead's ~20s CI budget. Override for a longer offline run:

```text
METTLE_FUZZ_ITERS=5000 cargo test -p als-syntax --test fuzz_mutations -- --nocapture
```

An offline run at `METTLE_FUZZ_ITERS=500` (**88,500 mutants**, ~127s) was
run during this session and passed clean (after the fix in §1.2 below).

### Bugs found → fixed

**Printer under-parenthesization after the Part-2 binder-composition fix**
(found by the offline `METTLE_FUZZ_ITERS=500` run, mutation `TokenSwap` on
`corpus/alloytools-models/models/examples/toys/ceilingsAndFloors.als`,
iteration 187). Once the parser started rejecting a binder as the operand of
a comparison or a second composition hop (§2 below), the pretty-printer —
whose `needs_parens` decision only tracked "is this the tail of the
enclosing expression" (`rightmost`), not the parser's new hop-budget — kept
emitting some of those binders **bare**, producing text the parser itself
would then reject: a genuine round-trip break (property 3), not merely
non-minimal parentheses.

Root cause: `rightmost` and the new binder-composition budget are two
*independent* conditions (either alone can force parens), but the printer
only tracked the first. Fix: `crate::prec::child_binder_budget` (and the
`BINDER_BUDGET_{NONE,HOP,TOP}` levels) moved out of `parser.rs` into
`prec.rs` — the same "shared table" pattern the module already used for
binding powers — so the printer can independently re-derive the identical
budget the parser would have had at every position, and
`Pretty::needs_parens` now requires **both** `rightmost` and
`budget >= BINDER_BUDGET_HOP` before omitting parens around a `Quant`/`Let`
node. `crates/als-syntax/src/print.rs`'s `write_expr`/`write_operand`/
`write_unary`/`write_binary`/`write_arrow`/`write_ite`/`write_closure`/
`write_word_prefix` all thread the budget through exactly as the parser's
`parse_operand`/`parse_prefix`/`build_infix`/`build_implies` do. Verified:
the original 88,500-mutant offline run, re-run after the fix, passed clean;
167/167 corpus round-trip unaffected.

### Deep-nesting verdict

**A depth guard was required** (not "measured safe without one"). Before any
guard, deliberately pathological nesting (`(`, `{`, quantifier chains)
**stack-overflows the debug build (SIGABRT, unrecoverable)** well within a
realistic fuzz budget — first observed via `mettle parse` on a 3,500-level
`{`-nested file (main OS thread, ~16 MiB stack on this machine), and
independently via the fuzzer's own `deep_nesting_stressors_never_crash`
test crashing a `cargo test` worker thread (whose stack is considerably
smaller than a subprocess's OS default).

**Measurements** (debug build, deliberately shrunk thread stacks via
`std::thread::Builder::stack_size`, one probe per OS process so a crash
never kills the search):

| Construct | Stack-frames per nesting level | Max safe unguarded depth @ 1 MiB stack | Max safe unguarded depth @ 2 MiB stack |
|---|---:|---:|---:|
| `(…)` / `{…}` (parser recurses through the whole Pratt chain: `parse_operand` → `parse_prefix` → … → `parse_atom` → `parse_expr` → back to `parse_operand`) | ~9 | 212 levels | 429 levels |
| `~`/`^`/`*` chain (`parse_closure` self-recursion only) | ~2 | 20,000+ (no crash observed) | 20,000+ |

`(`/`{` is the worst case by a wide margin — the guard is sized against it.

**Fix:** `MAX_EXPR_DEPTH = 256` (`crates/als-syntax/src/parser.rs`), an
explicit `depth: u32` counter on `Parser`, incremented/decremented around
`parse_operand`/`parse_closure` (the two genuinely-recursive entry points;
every other function in the Pratt core recurses *through* one of these), a
new `ParseError::TooDeep` variant carrying a span. `(`/`{` cost 2 counter
units per nesting level (matching the 9-frame chain above), so `256` fires
at 128 real `(`/`{` levels — comfortably under the measured 212-level floor
at 1 MiB, verified safe (no crash) even against **100,000** adversarial
`(`/`{`/`~` nesting levels on an explicit 1 MiB debug thread.
Two orders of magnitude past anything a real model approaches (the vendored
corpora never exceed a handful of nesting levels). One jar probe (`java -cp
… OracleShim`, `run { ((((...))))  }` at ~5,000 levels) confirms the
reference throws a raw `StackOverflowError` on the same shape — mettle's
`TooDeep` is a deliberate, better-than-reference divergence (LIMITATIONS.md).

**Regression tests** (`crates/als-syntax/src/parser/tests.rs`, "Deep-nesting
guard" section): a quantifier chain (~1 depth-unit per level, the cleanest
1:1 proxy) at `MAX_EXPR_DEPTH - 10` parses; at `MAX_EXPR_DEPTH + 10` yields
`TooDeep`; `(`/`{`/`~` nesting at `MAX_EXPR_DEPTH` levels each independently
confirmed to hit `TooDeep`, not crash. The CLI (`mettle parse`) renders
`TooDeep` through the same caret-diagnostics path as every other
`ParseError` (verified manually — no special-casing needed).

### A second, deliberately out-of-scope finding: printer recursion depth

The "long operator chains" stressor (`long_operator_chains_parse_without_crashing`)
found that the **printer** (`print::pretty_to_string`/`dump`), not the
parser, can stack-overflow on a sufficiently long *flat* operator chain
(`A + A + … + A`, thousands of terms): the parser's Pratt loop handles a
left/right-associative chain **iteratively** (verified safe parsing
10,000-term chains even on a 1 MiB thread), but the resulting AST is a
deeply *left-leaning* tree, and the printer's `write_expr`/`write_binary`
(and `dump`'s `Dumper::expr`) walk it with ordinary unguarded recursion —
depth there equals chain length, not the parser's bounded recursion count.
Measured: a 5,000-term chain crashes a debug build's printer on a small
thread stack even though the identical chain parses fine.

This is a genuine finding but **out of this bead's parser-robustness scope**
and not fixed here: `Pretty`/`dump`'s public API is `Display`/plain-`String`
based (mt-012's deliberate design, `PORTING_RULES` R9d), and a `Display`
implementation that returns `Err` deep in a formatting call is documented by
`std` to make `to_string()` **panic** anyway — so a depth guard there would
only turn one stack-overflow-flavor crash into a panic-flavor one, not a
clean `Result`, without also reworking `Ast::pretty`/`pretty_to_string`'s
public signature (which many call sites — the CLI, snapshot tests,
`corpus_roundtrip.rs` — depend on staying infallible). The fuzzer's own
round-trip check is therefore capped at a measured-safe chain length
(`moderate_operator_chains_round_trip`, 300 terms, verified safe even at 512
KiB) so this test suite stays reliable in CI; the parser-only stress check
(`long_operator_chains_parse_without_crashing`) still exercises the full
10,000-term range, since parsing alone is proven safe there. Flagged as a
candidate follow-up bead (printer/dumper depth safety) rather than folded in
here.

## 2. Part 2 — Binder-composition rule

### Method

`crates/als-conform/shim/ParseOnlyShim.java` (already built for mt-013) run
in batch mode against a programmatically-generated probe matrix: binder
kinds (`all no some lone one sum let`) × enclosing operators across every
precedence tier (`;` `or` `iff` `implies` `and` `until/releases/since/
triggered`, comparisons, `+ & -> . <: :>`) × composition depth 1–3 × prefix
wrappers (`! always no # ~`) × the `implies … else` then/else distinction,
plus the exact `q or r and all x: A | body` bug shape and its documented
single-hop-accepted siblings. **217 probes total** (200 in the first batch,
17 targeted follow-ups to resolve two ambiguous cases), one JVM batch run
(`ParseOnlyShim`, <1s), cross-checked against mettle's *fixed* parser with
**zero mismatches**.

### Results by category

| Category | n | Jar accepts (syntax-OK) | Jar syntax-rejects |
|---|---:|---:|---:|
| Depth-1, single formula operator (`or iff implies and until…`) × 7 binder kinds | 56 | 56 | 0 |
| Depth-1, relational operators (`+ & -> . <: :>` × `in`) × {`all`,`sum`} | 14 | 12 | 2 (`in` only) |
| `;` alone (field-bound housing) | 7 | 7 | 0 |
| Depth-2, outer(weaker) wraps inner(stronger) wraps binder, all formula-op pairs | 44 | 10 (all `implies`-outer) | 34 |
| Same-tier chain (`q and r and … and binder`) | 8 | 8 | 0 |
| `;` as outer wrapping a depth-1 inner op | 8 | 8 | 0 |
| Depth-3, three distinct formula ops | 10 | 0 | 10 |
| Prefix wrappers over a bare binder (`! always no # ~`) × 7 binders | 35 | 28 (all but `no`) | 7 (`no` only) |
| `implies … else`, binder in **then** (wrapped or bare) | 8 | 0 | 8 |
| `implies … else`, binder in **else** (wrapped or bare) | 7 | 7 | 0 |
| Documented control shapes (the exact bug + its accepted siblings) | 3 | 2 | 1 (the bug shape) |

("Jar accepts" folds in the reference's later-phase `other`-category
failures — type/resolution errors, out of Rung-1's scope — which count as
syntactically OK for this comparison, exactly as in mt-013.)

### The rule (M2)

> A binder (`let`/quantifier) may be the rightmost operand of **exactly one**
> enclosing operator "hop" — including a left-associative chain of the
> *same* operator, which is one hop, not many — and a **second**, distinct
> hop is rejected **unless** the enclosing operator is a bare `implies`
> (`=>` with no `else`) or the `else` branch of `implies … else`, either of
> which refreshes the budget to a fresh two-hop allowance for its own
> branch (but grants nothing further beyond that); comparisons
> (`= in < > <= >= …`) and the set-test prefixes (`no some lone one set
> seq`) never accept a binder operand **at all**, at any budget; and the
> `implies … else` **then**-branch (when an `else` *does* follow) never
> accepts one either, even bare.

Concretely, as an integer "budget" (`crate::prec::child_binder_budget`):
`TOP` (2) at a fresh expression start; an ordinary operator's right operand
gets `HOP` (1) only if the ambient budget was `TOP`, else `NONE` (0);
`implies`'s then-branch (no `else`) and `implies…else`'s else-branch get
`TOP` under the same condition; comparisons and `implies…else`'s
then-branch are `NONE` unconditionally; a bare binder needs `budget >=
HOP`. A **parenthesized** binder is unaffected by any of this — parens
always re-enter the grammar fresh (`TOP`), which is why e.g.
`q or r and (all x: A | body)` stays legal.

This was derived, not assumed: the naive theory ("any looser operator can
reach the binder via normal precedence fall-through") was falsified by the
depth-2 data (only `implies`-outer succeeds, not `or`/`iff`/`and`-outer,
even though all of them are "looser" than the inner operator); the correct
model came from tracing exactly which `parse_operand`/`build_infix` call
"found" each operator token (the true top-level entry's own Pratt loop, vs.
a nested call reached via a *different* enclosing operator's loop) and
matching that against every probe, including the trickier ones (`implies`
reached from within an *ineligible* enclosing operator's loop does **not**
get its usual bonus — H-category probes in the raw data — confirming the
budget is inherited, not intrinsic to the `implies` token).

### Fix

Implemented exactly as derived: `crates/als-syntax/src/prec.rs` gained
`BINDER_BUDGET_{NONE,HOP,TOP}` and `child_binder_budget` (shared by parser
and printer, see §1.2); `crates/als-syntax/src/parser.rs`'s
`parse_operand`/`parse_prefix`/`parse_postfix`/`parse_dot_rhs`/
`parse_closure`/`build_infix`/`build_implies` all thread an explicit
`budget: u8` parameter; a new `ParseError::BinderNeedsParens` variant
("a quantified formula here must be parenthesized") replaces the generic
"expected an expression" wherever the budget forbids a binder that's
actually present. `implies … else`'s then-branch needed one deliberate
extra trick: since the parser doesn't know an `else` is coming until *after*
parsing the then-branch, `build_implies` tries the maximally-restricted
parse first (cheap, and correct for the overwhelming majority of real code
which has no binder there at all) and only backtracks to retry at the full
budget if that fails — then rejects with `BinderNeedsParens` if `else`
follows *and* the retry needed the extra budget (i.e., a bare/composed
binder was actually used there).

**Regression tests** (`crates/als-syntax/src/parser/tests.rs`, "Binder-
composition budget" section, 9 tests): the exact bug shape now fails with
`BinderNeedsParens`; every single-hop and `implies`-two-hop shape the jar
accepts still parses; same-tier chains of arbitrary length still parse;
comparisons and set-test prefixes never accept a bare binder; `implies …
else`'s then-branch never does (bare or composed) while its else-branch
does; ordinary prefixes stay transparent to composed (not just bare)
binder operands; parenthesized binders bypass the whole budget regardless
of position.

**Gauges:** 167/167 corpus lex/parse/round-trip preserved (no corpus file
relied on the over-permissive shape — expected, since the corpus is
jar-derived); full workspace `cargo fmt --check`/`cargo clippy --workspace
--all-targets -- -D warnings`/`cargo test --workspace` green.

### mt-026 — prefix-wrapping-the-binder refinement

mt-020/025's alloy4fun differential (`docs/reference/alloy4fun-resolve-pass.md`
§10) left exactly 6 real-world codes where the jar rejects at parse time
(`ParseOnlyShim` category `syntax`) and mettle over-accepted: `019940`,
`023314`, `023316`, `029402`, `120634`, `137967` — all the same shape,
`… and always all f: … | …` / `… and not some x: … | …` /
`… iff not some x: … | …`. Every one is a prefix operator (`always`/`not`)
sitting directly between an ordinary infix formula operator (`and`/`iff`)
and a binder.

**Root cause:** the original Part 2 derivation above never actually tested
this shape. `ordinary_prefixes_are_transparent_to_the_budget` (the
regression test that seemed to cover it) instead tests a prefix wrapping
the infix's *left* operand (`always q and all x: A | …`, prefix binds to
`q`) — a trivially different, already-legal case. A prefix *wrapping the
binder itself*, composed with an enclosing infix operator's single hop,
was an untested gap, and mettle's `parse_prefix`/`parse_closure_at_depth`
happened to implement the more permissive (wrong) reading: "every ordinary
prefix passes its ambient budget through unchanged, period."

**Method:** two rounds of fresh `ParseOnlyShim` probes against the pinned
jar (2026-07-16, disjoint from the original 217): round 1 (427 probes)
swept every ordinary prefix (`! not always eventually before after
historically once # ~`) × every binder kind (`all some no lone one sum
let`), each combination probed bare at a fresh top-level start, doubled
and chained 3–5 deep at a fresh start, and as the RHS of `and`/`or`/`iff`/
a bare `implies` (plus a no-prefix `and`-RHS control per binder kind);
round 2 (33 targeted follow-ups) covered every other ordinary infix tier
(`until releases since triggered`), every relational operator (`+ & -> .
<: :>`), same-tier chains, `implies`'s second hop, and `implies … else`'s
both branches.

### Results by category (round 1 + 2, prefix-wraps-binder shape only)

| Context | n | Jar accepts (syntax-OK) | Jar syntax-rejects |
|---|---:|---:|---:|
| Bare top-level, 1 prefix × 7 binders × 10 prefixes | 70 | 70 | 0 |
| Bare top-level, 2 prefixes (chained) × 7 × 10 | 70 | 70 | 0 |
| Bare top-level, 3–5 prefixes chained (`!`/`always` only) | 12 | 12 | 0 |
| RHS of `and`, no prefix (control) × 7 binders | 7 | 7 | 0 |
| RHS of `and`, 1 prefix × 7 binders × 10 prefixes | 70 | 0 | 70 |
| RHS of `or`, 1 prefix × 7 × 10 | 70 | 0 | 70 |
| RHS of `iff`, 1 prefix × 7 × 10 | 70 | 0 | 70 |
| RHS of bare `implies`, 1 prefix × 7 × 10 (control) | 70 | 70 | 0 |
| RHS of `until`/`releases`/`since`/`triggered`, 1 prefix (`not`) | 4 | 0 | 4 |
| RHS of `+ & -> . <: :>`, 1 prefix (`~`, tier-legal everywhere) | 6 | 0 | 6 |
| Same-tier chain (`q and r and always all …`) | 1 | 0 | 1 |
| `implies`'s second hop (`q implies r and always all …`) | 1 | 0 | 1 |
| `implies`'s own branches (then/else), 1 prefix | 2 | 2 | 0 |

("Jar accepts" folds in later-phase `other`-category failures, same
convention as the original table.)

### The refinement (M2′)

> A prefix operator (`!`/`not`, the temporal unaries, `# int sum`, the
> closure operators `~ ^ *`) forwards its ambient binder-composition budget
> to its own operand **unchanged only while that ambient budget is still
> `TOP`** (a fresh expression start, or one of `implies`'s refreshed
> branches) — chained arbitrarily deep, still transparent
> (`! ! ! all x: A | …`, `always always always all x: A | …` both parse).
> Once the ambient budget has already been spent to `HOP` by an enclosing
> ordinary infix operator's one hop, a prefix wrapping a binder does **not**
> forward that `HOP` — it collapses to `NONE`, rejecting the binder,
> uniformly across every ordinary infix tier, every relational operator,
> and every prefix/binder kind, even though the *un-prefixed* bare binder
> in the identical slot stays legal (`q and all x: A | …` parses;
> `q and always all x: A | …` does not). M2's original rule (the budget
> arithmetic across infix operators: one hop, `implies` refreshes to two,
> comparisons hard-block) is otherwise unchanged.

Concretely: `crate::prec::prefix_operand_budget(budget)` returns `budget`
unchanged if `budget >= BINDER_BUDGET_TOP`, else `BINDER_BUDGET_NONE`. This
single function is the whole fix — it replaces the previous "pass `budget`
straight through" behavior at every prefix call site.

### Fix

`crates/als-syntax/src/prec.rs` gained `prefix_operand_budget`, doc-linked
next to `child_binder_budget` as the same kind of shared parser/printer
source of truth. `crates/als-syntax/src/parser.rs`: `parse_prefix`'s
non-`TIER_TEST` branch and `parse_closure_at_depth` (the `~ ^ *` operators,
which recurse outside `parse_prefix`) both now compute
`prefix_operand_budget(budget)` before recursing into their operand instead
of forwarding `budget` verbatim. `crates/als-syntax/src/print.rs`:
`write_unary`'s `Not`/`Always`/`Eventually`/`After`/`Before`/
`Historically`/`Once`/`Card`/`IntOf`/`SumOf` arms and the three
`write_closure` call sites (`Transpose`/`Closure`/`ReflexiveClosure`) now
pass `prefix_operand_budget(budget)` for the operand's own composition
budget instead of `budget`, so the printer independently re-derives the
identical parenthesization decision (mt-014's shared-table discipline,
LESSONS.md: "parser AND printer must move in lockstep").

**Regression tests** (`crates/als-syntax/src/parser/tests.rs`, "mt-026:
prefix-wrapping-the-binder is TOP-only transparent" section, 6 tests): a
chain of up to 5 prefixes at a fresh start still parses; the exact 6
real-world bug shapes (minimized to `q and always all x: A | x in x`,
`q and not some x: A | x in x`, `q iff not some x: A | x in x`, each
jar-verified directly with `ParseOnlyShim` — category `syntax`, "35/18
possible tokens" error at the binder keyword) now fail with
`BinderNeedsParens`, while their un-prefixed bare-binder siblings still
parse; the rejection generalizes across every ordinary infix tier, every
relational operator, and `~`; same-tier chains and `implies`'s second hop
stay rejected too; `implies`'s own then/else branches (refreshed `TOP`)
stay fully transparent to a prefix-wrapped binder.

**Gauge:** re-ran `resolve-gauge alloy4fun` (150,891 codes) and diffed
against the cached jar verdicts — **exactly** the 6 target codes flipped
from over-accept to agree-reject (`ok:false` both sides, jar `category:
syntax`, mettle `phase: parse, variant: OpenedFileParse`); zero other
files changed status in either direction. Over-acceptance: **320 → 314**
(total agreement 99.7879% → 99.7919%, still rounding to **99.79%** — the
6-code fix is real but small against 150,891 codes), 0 jar-accepts/
mettle-rejects both directions preserved. `als-syntax`'s
corpus_lex/parse/roundtrip suites (the syntax-level equivalent of the
167-file curated-corpus gate; the `resolve-gauge paths` resolve/type gauge
is out of this bead's als-syntax-only scope): still 167/167. Full
`als-syntax` test suite (151 unit + corpus lex/parse/roundtrip + mutation
fuzzer, 4,248 mutants) green; `cargo fmt --check`/`cargo clippy -p
als-syntax --all-targets -- -D warnings`/workspace build green.

## 3. Definition-of-done check

- Fuzzer: deterministic (verified via repeat runs), all properties held
  over the default budget (4,248 mutants) and an offline 88,500-mutant run;
  offline override documented in the test's own doc comment.
- Deep-nesting: resolved with a guard + typed error + regression tests
  (guard was required — measured crash without one); jar comparison probe
  confirms a deliberate, better-than-reference divergence.
- Part 2: jar rule mapped (table above), fix implemented, regression tests
  both directions, `LIMITATIONS.md` entry resolved,
  `alloy4fun-error-pass.md` §4 appended per the brief.
- One genuine fuzzer-found bug (printer under-parenthesization) fixed with
  a shared parser/printer budget table, verified against the full offline
  run.
- One genuine fuzzer-found finding (printer recursion depth on long flat
  chains) documented as deliberately out of scope, with a bounded,
  CI-safe test in place rather than an unbounded one.
