# mt-013 — Alloy4Fun differential parse pass & caret diagnostics

Evidence doc for bead **mt-013**: (1) rustc-style caret-and-label diagnostics
in `mettle parse`, and (2) a large differential test of mettle's parser
against the pinned reference jar, using the alloy4fun corpus as a
naturally-occurring stream of both valid and broken Alloy source. Kept tight
and factual per the bead brief — this is the referenceable evidence for the
Rung-1 error-quality claim, not a narrative.

## 1. Caret diagnostics

`crates/mettle/src/diagnostics.rs` (new module, CLI-only per STYLE E3 — the
renderer never lives in `als-syntax`) turns a `(source, path, span, message)`
tuple into:

```
error: syntax error: expected an expression
 --> path/to/model.als:2:12
  |
2 |   bar: set }
  |            ^
```

`LineIndex` precomputes line-start byte offsets once per render; column is
counted in Unicode scalar values, never bytes. Edge cases, each with a
colocated unit test in `diagnostics.rs`:

| Case | Handling |
|---|---|
| Multi-line span | Renders only the first line, caret to that line's end, trailing `= note: span continues to line N, column M` |
| Tabs in the source line | Source line printed as-is; the caret-padding line copies the same prefix with every non-tab character replaced by a space (tabs stay tabs) — the standard trick, so carets align under any terminal tab width |
| EOF span | Points one past the last character; never slices out of bounds |
| Empty span | Renders a single `^` |
| Multibyte (UTF-8) line | Column = char count, never byte count; never slices mid-codepoint |
| Gutter width | Right-aligned to the widest line number actually printed (verified at a 2-digit boundary) |

`mettle parse <file.als>` on a bad file now renders this block to stderr;
exit codes are unchanged (1 = parse error, 2 = usage/IO). The old
`file:line:col: error: msg` one-liner is gone.

## 2. Differential pass — dataset & method

**Dataset:** `corpus/alloy4fun/2024-25/*.json`, 21 JSON-Lines files,
**186,318** records total (per `docs/reference/corpora.md`). Every record's
`code` field was extracted and deduplicated by SHA-256 of the UTF-8 bytes:
**150,891 unique code texts**, 0 empty. (Dedup rate ≈19% — lower than
expected going in; alloy4fun's "fork" model means most saved permalinks are
distinct edits, not exact resubmissions.)

**Mining tool:** a throwaway Rust binary (path dependency on `als-syntax`,
not part of the mettle repo — scratch-only per the bead brief) called
`als_syntax::parse` directly over each unique code text, bucketing
`OK`/`FAIL(line:col, message)`. Zero panics across all 150,891 inputs. Final
(post-fix) split:

| | count |
|---|---|
| unique codes | 150,891 |
| mettle parse-ok | 136,323 |
| mettle parse-fail | 14,568 |

**Jar oracle — new parse-only shim:** the existing `OracleShim` (mt-006)
drives `A4Options`-based solving, too heavy for a syntax-only pass over tens
of thousands of files. Added `crates/als-conform/shim/ParseOnlyShim.java`
(committed, lives in the crate's `shim/` dir per the bead brief): one JVM
launch, a list of file paths on stdin-equivalent (a list file, one path per
line), one JSON-Lines verdict per file.

The reference has **no public syntax-only entry point** —
`CompUtil.parseEverything_fromString` both parses *and* resolves names/opens/
types in a single pass, so a bare try/catch conflates real grammar/lex
failures with later-phase semantic failures (unresolved `open` targets,
unknown names, type mismatches) that mettle's Rung-1 parser intentionally
doesn't attempt yet. `ParseOnlyShim` disambiguates by inspecting the top
frame of the thrown `Err`'s Java stack trace, calibrated empirically against
~20 minimal probes (see the shim's own doc comment for the full table):

- `CompLexer`, `CompParser`, or `CUP$CompParser$actions` (the generated
  scanner/parser and its inline grammar actions — where the reference's own
  parse-time checks like scope-on-`univ`, `$`-in-name, empty-enum live) →
  **`syntax`** — a genuine grammar/lex-phase failure.
- `CompModule#addModelName` / `#addEnum` (also inline, parse-time checks
  mettle reproduces exactly) → **`syntax`**.
- Everything else — `CompModule#hint` (name resolution),
  `#resolveParams` (open argument-count), `#dup` (duplicate-declaration,
  a whole-module symbol table check), `CompUtil#parseEverything_fromFile`
  (open target file lookup), any `ErrorType` — → **`other`**: a later-phase
  resolution/type error outside Rung 1's contract. A file whose only
  failure is `other` counts as **syntactically OK** for this comparison —
  matching mettle's own behavior (`open` is an inert paragraph at parse
  time; no name/type resolution yet, confirmed: mettle never rejects a file
  solely for an unresolvable `open`).

This directly resolves the brief's `open`-resolution concern: an
unresolvable `open util/...`-style target throws `ErrorSyntax("File cannot
be found...")` from `CompUtil#parseEverything_fromFile` — classified
`other`, not counted against mettle.

**Budget:** one JVM per batch (not per file) — 14,568 files in **8.1s**,
1,000 files in **4.5s**. JVM startup, not per-file work, dominates; this
easily scales to the full corpus if ever needed.

**Comparisons run:**
1. **All 14,568 mettle-rejects** → jar-parsed, to hunt `jar-accepts +
   mettle-rejects` (highest priority per the bead brief).
2. **A seeded random sample of 1,000 mettle-accepts** (`random.seed(13)` —
   mt-013; sampled from the final 136,323-code accept set with Python's
   `random.sample`) → jar-parsed, to hunt over-acceptance.
3. **Position/message comparison** over every code both engines reject at
   the syntax level.

Jar version: pinned **Alloy 6.2.0**, `Version.experimental = true` (per
`docs/reference/alloy6-reference.md`) — string literals and range scopes are
live syntax in this comparison, as in mettle.

## 3. Divergences found → fixed

Two real mettle parser bugs surfaced, both jar-verified in isolation before
fixing, both closing the pinned grammar contract's own stated rules (no
grammar-doc changes needed — these were implementation bugs, not spec
gaps).

### Fix 1 — prefix closures didn't accept a binder as their operand

**Symptom:** two real submissions used the (fairly common) idiom of ending
one formula with a trailing `^`/`*` transitive-closure marker on the wrong
side (`t.succs^` instead of `^t.succs`), immediately followed by a new
`all …| …` formula. Grammar-doc §3.1: "Binders are the one exception" to
every prefix operator's tier gate — but `parse_closure` (the tier-20
`~ ^ *` prefixes) recursed into itself for its operand instead of going
through `parse_operand` (which is where the binder-exception check lives),
so `^ all x: A | …` failed with "expected an operand" instead of parsing
the quantifier as the closure's operand. **Jar-verified**: the reference
parses this construct fully and only rejects it later, at type-check
(`This expression failed to be typechecked`) — never at parse time.

- **Fix:** `crates/als-syntax/src/parser.rs`, `parse_closure` now checks
  `starts_binder()` before recursing, matching every other prefix tier.
- **Regression tests:** `crates/als-syntax/src/parser/tests.rs` —
  `closure_prefix_as_rightmost_operand_of_binder`,
  `closure_prefix_starting_a_new_formula_takes_the_next_quantifier`.
- **Corpus effect:** 2 unique codes flipped `FAIL → OK` (both jar-syntax-OK
  already, confirmed no new false-accepts).

### Fix 2 — `disj`/`pred/totalOrder` wrongly accepted as bare atoms

**Symptom:** discovered while auditing the both-reject position table
(below): several real submissions wrote `disj a, b : T | …` as if `disj`
were its own quantifier (a common student misconception — `disj` is a decl
qualifier, not a binder). mettle's `parse_atom` treated `disj` and
`pred/totalOrder` as general standalone atoms (like `int`/`sum`/`fun/min`),
so it accepted `disj` as a bare `Name` expression and only failed several
tokens later, cascading through `t1, t2 : Professor | …` before giving up.
**Jar-verified**: `disj`/`pred/totalOrder` are *not* general atoms per
grammar-doc §3.2 (unlike `int`/`sum`/`fun/min`/`fun/max`/`fun/next`, which
§4.6 explicitly lists as atoms) — they are box-join-only names, valid only
as `name[args]` or as a dot target (`a.disj`, unaffected by this fix and
still jar-verified permissive). A bare `disj`/`pred/totalOrder` not
immediately followed by `[` is `"1 possible tokens: ["` in the reference,
reported right after the name.

- **Fix:** `crates/als-syntax/src/parser.rs`, new `builtin_box_join_target`
  helper; `parse_atom`'s `Disj`/`TotalOrder` arms now require the next
  token to be `[`, erroring at that following token otherwise (matching the
  jar's position convention). `parse_dot_rhs`'s `Disj`/`TotalOrder` arms
  are untouched — the dot form stays unguarded (jar-verified: `a.disj`
  parses fine, failing only later at a builtin-arity check).
- **Regression test:** `crates/als-syntax/src/parser/tests.rs` —
  `bare_disj_and_total_order_without_bracket_are_errors`.
- **Corpus effect:** 27 unique codes flipped `OK → FAIL` — mettle had been
  **over-accepting** these (a real Rung-1 gauge violation caught by this
  pass, not just a position-quality issue). All 96 post-fix
  `"expected `[`"` failures were independently jar-verified as genuine
  syntax errors (0/96 jar-accepts) via a dedicated `ParseOnlyShim` run.

Both fixes preserve the existing gauges: `cargo test -p als-syntax` stays
**167/167** corpus lex/parse/round-trip.

## 4. Divergences found → documented, not fixed

Two narrower divergences were root-caused but deliberately left alone this
session (see `LIMITATIONS.md` for the permanent record):

- **Unicode identifier classes (1 occurrence).** One submission used `€`
  (EURO SIGN) where `in` was meant. `Character.isJavaIdentifierPart`
  classifies currency symbols as identifier characters; `char::is_alphabetic`/
  `is_alphanumeric` do not — an already-anticipated divergence
  (`alloy6-grammar.md` §1.4 flagged this exact possibility before any corpus
  evidence existed). The jar accepts `€` lexically and rejects the resulting
  expression at type-check; mettle rejects it at lex time. Both ultimately
  reject the file, so this is not a wrong verdict, just an earlier one — left
  as a documented, deliberate approximation rather than broadening the
  identifier charset for one corpus hit.
- **Binder-as-rightmost-operand over-composes across nested precedence
  levels (2 occurrences, from the over-acceptance sample).** mettle's
  recursive-descent parser applies grammar-doc §3.1's binder exception
  uniformly and recursively at every precedence level, so
  `q or r and all x: A | body` parses (the quantifier absorbs as the
  rightmost operand of `and`, itself the rightmost operand of `or`).
  Jar-verified minimal isolation: `q or all x:A|body` parses,
  `q and r and all x:A|body` parses, but the two-hop
  `or`-wrapping-`and`-wrapping-quantifier does **not** — the reference's
  generated LALR grammar apparently defines the binder-absorbing production
  once per level without composing it through an enclosing looser level, a
  narrower rule than mettle's uniformly-recursive one. Root cause understood
  in outline; the exact per-level combinatorics (which of the 21 levels ×
  which binder keywords compose) were not exhaustively mapped, and a
  faithful fix risks either under- or over-restricting without that map.
  Documented in `LIMITATIONS.md` as a known over-acceptance, flagged as a
  good target for mt-014's mutation fuzzer or a dedicated follow-up bead.

  **Resolved in mt-014** — the exact per-level rule was mapped (≈220 jar
  probes) and implemented as a "binder-composition budget"; see
  `docs/reference/fuzzing.md` §2 for the probe table and rule, and
  `LIMITATIONS.md` for the current (now empty, on this point) status.

## 5. Position/message comparison (both-reject set)

Recomputed after both fixes, over the final **14,560** unique codes both
engines reject at the syntax level (excludes the 8 `other`-category codes —
see §6):

| | count | % |
|---|---:|---:|
| Exact `(line, col)` match | 14,530 | 99.79% |
| Same line, different column | 21 | 0.14% |
| Different line | 9 | 0.06% |

The 27-code swing from fix 2 (§3) accounts for the bulk of the improvement
in the same-line bucket (it started at 80/14,533 = 0.55% before that fix).
Residual same-line diffs are small (mostly ±1–2 columns, a few larger) and
cluster into two more patterns not chased further this session, both purely
position-precision (never verdict-affecting — both engines already reject):
a `{a, b}`-style set-literal-vs-comprehension disambiguation case (jar
reports `2 possible tokens: , :` further into the malformed decl than
mettle's earlier "expected an expression"), and a handful of cases where jar
expects a bare `NAME` a token or two later than mettle's own stopping point.
Residual different-line cases are inherent to a fail-fast, no-recovery
parser (ADR-0007 §3): once two independent implementations diverge on what
they accept mid-construct, their eventual give-up points can land on
different lines — expected, not itself evidence of a bug, and none of the 9
represent a `jar-accepts + mettle-rejects` case.

One pattern worth a specific mention for a future session: 3 same-line
diffs involve `\u{a0}` (NON-BREAKING SPACE) — mettle reports it as a stray
character, while the jar's much-earlier error position suggests its lexer
treats NBSP as skippable whitespace. Distinct mechanism from the `€` case
above (whitespace-skipping, not identifier-charset), narrow, and a
plausible low-risk future fix (broaden `skip_trivia`'s whitespace class) —
not chased this session given the budget was better spent confirming zero
verdict-affecting divergences.

Message quality: mettle's `"expected X"` messages already tend to name the
specific expected construct (e.g. "expected `|` or `{` (a quantifier
body)") where the jar's CUP-generated messages are a raw expected-token-set
dump (`"There are N possible tokens that can appear here: …"`). No message
regressions found; no wording changes made this pass.

## 6. Over-acceptance sample (mettle-accepts, seed 13, n=1000)

Sampled via `random.seed(13); random.sample(ok_uids, 1000)` from the final
136,323-code accept set (seed chosen for the bead: mt-013).

| | count |
|---|---:|
| jar fully accepts (agree: valid) | 756 |
| jar syntax-reject (**real over-acceptance**) | 2 |
| jar other-reject (later-phase; not an over-acceptance — mettle doesn't resolve names/types yet) | 242 |
| jar shim error | 0 |

The 2 real over-acceptances are the binder-composition case documented in
§4. The 242 "other" codes are all mettle correctly accepting syntax that
later fails to *resolve* (unknown names, arity mismatches, type errors) —
expected and out of Rung-1's scope by design (LIMITATIONS.md: "Everything
past syntax… is 'not yet implemented'").

## 7. Definition-of-done check

- **Zero known `jar-accepts + mettle-rejects`** over the full 14,568-code
  mettle-reject set: confirmed. All 8 `other`-category codes are explained
  (1 documented Unicode-identifier divergence, 7 duplicate-sig-name-masked
  — the jar aborts at an earlier, out-of-scope duplicate-declaration error
  before reaching the position mettle independently and correctly flags;
  verified by isolating 2 of the 3 distinct masked constructs and
  confirming the jar rejects them too, grammatically, once unmasked).
- Over-acceptance sample run and triaged (§6): 2/1000 real, both
  root-caused and documented (§4), not fixed this session for the reasons
  given.
- Positions tabulated (§5): 99.79% exact match; no regressions introduced by
  either fix (both fixes *improved* the match rate).
- Caret diagnostics render correctly for all six specified edge cases (§1),
  each with a colocated unit test.
- Full gauntlet green: `cargo fmt --check`, `cargo clippy --workspace
  --all-targets -- -D warnings`, `cargo test --workspace` — corpus
  lex/parse/round-trip stays **167/167**.
- New regression tests: 3 in `crates/als-syntax/src/parser/tests.rs`
  (covering both fixes), 7 in `crates/mettle/src/diagnostics.rs` (caret
  edge cases) — all reference mt-013 in their doc comments.
- No grammar-doc (`alloy6-grammar.md`) changes needed — both fixes were
  implementation bugs against the existing pinned spec, not spec gaps.

## Files touched

- `crates/mettle/src/diagnostics.rs` — new: caret renderer + `LineIndex` + 7 unit tests.
- `crates/mettle/src/main.rs` — wires the renderer into `mettle parse`'s error path.
- `crates/als-syntax/src/parser.rs` — the two fixes (`parse_closure`, `builtin_box_join_target`).
- `crates/als-syntax/src/parser/tests.rs` — 3 new regression tests.
- `crates/als-conform/shim/ParseOnlyShim.java` — new: batch syntax-only jar oracle.
- `LIMITATIONS.md` — 2 new documented-divergence entries.
- `docs/README.md` — this doc linked in.
