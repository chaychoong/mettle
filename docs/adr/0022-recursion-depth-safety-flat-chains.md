# ADR-0022 — Recursion-depth safety on pathologically long flat operator chains

**Status:** Accepted (tech-lead, 2026-08-22 — Option-B no-fork: the mt-014 `MAX_EXPR_DEPTH` precedent settles the typed better-than-reference rejection, and the jar's own raw `StackOverflowError` at the same order means there is no conforming behaviour to preserve, only a crash to replace with a diagnostic)
**Open follow-up:** a **pre-existing** exponential-backtracking bug in
`build_implies` turns any `TooDeep` raised under a nested `=>` chain into a
2^k time-and-memory blow-up, and this ADR's guard adds a cheaper trigger for it.
See "Follow-up blocker: `build_implies` turns any `TooDeep` into a 2^k
blow-up". Needs its own bead before the guard's diagnostic can be considered
safe on adversarial input.

**Date:** 2026-08-22
**Builds on:** [reference/fuzzing.md](../reference/fuzzing.md) §1 (mt-014's deep-nesting verdict, which set the `MAX_EXPR_DEPTH`/`TooDeep` precedent this ADR extends) and mt-014's second, deliberately out-of-scope finding, which this ADR re-measures.

## Context

mt-014 found that a long **flat** operator chain (`A + A + … + A`) parses
safely — the Pratt loop handles left/right-associative chains iteratively — but
produces a deeply **left-leaning** tree that the printer then walks with
ordinary unguarded recursion, so print depth equals chain length rather than the
parser's bounded nesting count. It filed the printer exposure as mt-021 and
recorded the parser as already guarded (`MAX_EXPR_DEPTH = 256`, `TooDeep`,
verified against 100,000 adversarial `(`/`{`/`~` **nesting** levels).

mt-021's brief inherited two assumptions from that framing. **Both are false,
and this ADR exists because measuring them changed the problem.**

### Measurement (release build, main thread, macOS default ~8 MiB stack)

One OS process per probe so a `SIGABRT` never takes the harness with it;
bisection script and generated inputs in `scratchpad/probe/mt021/`.

Corrected cross-shape × cross-consumer matrix (7 operator shapes × 4
consumers). Two harness classification defects were found and fixed mid-round —
`subprocess` reports a signal death as a **negative** code, not the shell's
`128+n`; and a TIMEOUT must be a third outcome, not folded into either — so the
first table produced was wrong in both directions and is superseded by this one.

| shape | parse (pretty) | parse --ast (dump) | check (resolve) | exec (lower) |
| --- | ---: | ---: | ---: | ---: |
| `union_plus` | 57,000 / 58,000 | 52,000 / 53,000 | 6,000 / 6,125 | 6,000 / 6,125 |
| `inter_amp` | 57,000 / 58,000 | 52,000 / 53,000 | 6,000 / 6,125 | 6,000 / 6,125 |
| `and_chain` | 57,000 / 58,000 | 52,000 / 53,000 | 6,000 / 6,125 | 6,000 / 6,125 |
| `or_chain` | 57,000 / 58,000 | 52,000 / 53,000 | 6,000 / 6,125 | 6,000 / 6,125 |
| **`join_field`** | 57,000 / 58,000 | 52,000 / 53,000 | **3,687 / 3,750** | **3,687 / 3,750** |
| `arrow` | typed `TooDeep` at any length — already bounded by `MAX_EXPR_DEPTH` | | | |
| `implies` | HANGS at 255 — a pre-existing guard defect, filed as **mt-103** | | | |

(`survived / first-crash`, release build, main thread.) Resolver and lowerer
crash at the same length on every shape, so lowering adds no measurable depth
over resolving.

**Bound arithmetic.** Worst genuine crash: `join_field` at **3,687**. The 4×
margin rule gives **3,687 / 4 = 921**, so the bound must be ≤ 921 — **768** is
the clean value under it (1,024 would be 3.6× and fails the rule). Resulting
ratios, all three recorded as required:

* **4.8×** below the worst measured crash (3,687);
* **6.8×** above the longest chain in the 150,891-code alloy4fun corpus (113 —
  an upper bound, being the total operator count in one code);
* **96×** above the longest chain in the 167-file vendored corpus (8).

Every crash is `rc=134` (`SIGABRT` — stack-overflow abort), i.e. unrecoverable,
not a `Result`.

**Falsified assumption 1 — "no `.als` file can trigger it end-to-end."** The
parser guard counts *nesting* depth, and a flat chain has nesting depth 1. A
plain source file therefore reaches the printer with a 58,000-deep tree and
crashes it. The exposure is a user-facing crash on ordinary CLI input, not just
a hazard for API users building ASTs programmatically.

**Falsified assumption 2 — "the remaining exposure is the printer."** The
resolver overflows on the same input **an order of magnitude earlier**
(≈5,700 vs ≈58,000). Fixing only `print`/`dump` would leave `mettle check` and
`mettle exec` crashing at one tenth the chain length, so a printer-only change
does not remove the user-facing crash — it only removes the crash from the one
entry point (`mettle parse`) that already survives ten times longer than the
others.

### Two anchors for any bound

**The reference is not safe here either.** The jar throws a raw
`java.lang.StackOverflowError` on the same input at 5,000 terms (measured at
5,000 / 20,000 / 60,000 via `ParseOnly`), which is the same order as mettle's
resolver threshold. Matching the reference would mean crashing too, so a
`TooDeep`-style rejection is a deliberate better-than-reference divergence —
exactly the precedent `MAX_EXPR_DEPTH` set and LIMITATIONS.md already records.

**Real models are five orders of magnitude away.** The longest same-line
operator chain across all 167 corpus files is **8 terms**
(`tso_transistency_perturbed_minimize.als:415`, and two siblings). Any bound in
the hundreds or thousands is unreachable by real input.

### What option (a) actually costs

The brief asked for this explicitly. `print.rs` is 1,645 lines whose expression
half is a **deeply mutual** recursion — `write_expr` (13 call sites),
`write_operand` (19), `write_unary`, `write_binary`, `write_arrow`,
`write_compare`, `write_ite`, `write_closure`, `write_word_prefix`,
`write_boxjoin` — every one threading indent, precedence, *and* the
binder-composition budget (`prec::child_binder_budget`) that mt-014 added
precisely so the printer could re-derive the parser's parenthesisation
decisions position by position. Converting that to an explicit worklist means
re-expressing the paren/precedence decision flow as an explicit state machine
in a component that is **round-trip load-bearing**: any paren or precedence
drift is a silent correctness bug, caught only by the 167/167 round-trip and
the fuzzer. `dump.rs` is the easy half; `print.rs` is not.

## Decision

**Recommend option (d), a parser-side chain-length guard, as the primary fix —
and do not ship a printer-only change as if it closed the exposure.**

Extend the existing `MAX_EXPR_DEPTH`/`TooDeep` machinery in
`crates/als-syntax/src/parser.rs` to also bound the length of a flat operator
chain, so an adversarial file is rejected at the same place and with the same
diagnostic as adversarial nesting already is. This is the only option that

* removes the **actual** user-facing crash, including the resolver's, because
  every downstream consumer (printer, dumper, resolver, lowerer, evaluator)
  receives an AST that is bounded by construction;
* lives in one place that already owns depth safety, with an existing error
  variant, an existing CLI diagnostic path, and an existing precedent;
* is anchored on both sides — the jar dies at 5,000, real models reach 8;
* keeps every public signature infallible, so `Display` stays honest.

Its cost, stated plainly: it does **not** protect an AST built programmatically
through the `als-syntax` API, since such an AST never passes the parser. That
residual is real but has no in-repo caller, and is the appropriate home for
option (c)'s documented bound.

## Alternatives considered

**(a) Iterative/worklist rendering in `print`/`dump`.** Keeps the infallible
signatures and fixes both the file path and the programmatic path for printing.
Rejected as the *primary* fix on two grounds: it leaves the resolver crashing at
one tenth the threshold, so the user-facing crash survives; and its diff is not
contained (see "What option (a) actually costs") in a round-trip-load-bearing
component. Worth revisiting as a follow-up once (d) has removed the crash, when
it can be judged on its merits rather than under time pressure.

**(b) Depth cap returning `Result` from `pretty`/`pretty_to_string`/`dump`.**
Honest about failure, but breaks every call site and cannot be threaded through
`Display`, whose `fmt` may only return `fmt::Error` — a unit type that carries
no diagnostic — and whose contract discourages failing for reasons other than
the underlying writer. That would either lose the error entirely at the
`Display` boundary or force callers off `Display`, which is the printer's
primary interface. Rejected.

**(c) Document a bound plus `debug_assert`.** Cheapest, and leaves release
builds crashable. Rejected as a primary fix; adopted as the *residual* handling
for the programmatic-AST path that (d) cannot reach.

## Consequences

* An adversarial file is rejected with `TooDeep` instead of aborting the
  process, at every entry point rather than only `mettle parse`.
* mettle accepts strictly less than before at the extreme, and diverges further
  from the reference — in the direction the reference itself cannot sustain
  (it `StackOverflowError`s at 5,000). To be recorded in LIMITATIONS.md
  alongside the existing `MAX_EXPR_DEPTH` divergence.
* The bound changes the accepted-language surface, so it needs the corpus
  round-trip (167/167) and the fuzzer battery as gates, and the cap must be
  chosen with the 8-term corpus maximum and the ~5,700-term resolver threshold
  both in view.
* The programmatic-AST path stays crashable in release builds until (a) or (c)
  is taken up.

## Follow-up blocker: `build_implies` turns any `TooDeep` into a 2^k blow-up

Found while re-verifying the cross-shape threshold table (mt-021 Phase 0,
second delegate, 2026-08-22). This is a **pre-existing** parser bug that the
guard shipped above does not cause but does make easier to reach. Full evidence
in `scratchpad/probe/mt021/NOTES.md`.

`build_implies` (`crates/als-syntax/src/parser.rs:1524-1560`) speculatively
parses an `=>`'s then-branch at `BINDER_BUDGET_NONE` and, **on any `Err`**,
rewinds `self.pos` and re-parses the same tokens at the ambient budget. `=>` is
right-associative, so k nested `=>` frames each retry their whole right subtree
when anything below them fails: **2^k parse attempts**, each allocating arena
nodes that are never reclaimed (the function's doc comment calls the abandoned
nodes "harmless … this path is rare" — neither holds once the retries nest).
Time and peak RSS both double per level, measured on `some A => … => ) }`, a
plain syntax error with no depth guard involved: k=20 → 0.15 s / 324 MB,
k=24 → 2.3 s / 5.1 GB, k=26 → 9.2 s / 20.5 GB. A ~400-byte file with ~40 nested
`=>` and a trailing syntax error is an unbounded time-and-memory denial of
service.

**This is what the `implies` row of the threshold table actually recorded.** It
is not a stack overflow: at 255 terms the process runs 153 s and dies `rc=137`
(`SIGKILL`, the memory killer) with empty stdout and stderr, and
`thresholds.py`'s `rc < 0 or rc >= 128` test — a correct "did not exit cleanly"
check — read that as a stack crash. The cliff sat exactly at `MAX_EXPR_DEPTH`
(254 terms fine, 255 explodes) because mt-014's `TooDeep` was the failure that
detonated it, and the cost was flat in chain length because it is a function of
the depth limit, not of the chain.

**`MAX_AST_PATH` adds a cheaper trigger.** The new budget raises the same
`ParseError::TooDeep` from inside the same `parse_operand` call that
`build_implies` retries, and it fires on inputs the old nesting guard let
through. Measured on the current tree, k nested `=>` over an 800-link join
chain (~1 KB of source): k=10 → 0.11 s, k=14 → 1.6 s, k=18 → 38.8 s, k=22 →
past 90 s. The guard is not wrong — its path budget is correctly marked and
restored on every `?`, so the retry starts from a clean counter and nothing is
falsely rejected — but it widens the set of inputs that reach the blow-up.

Narrowing the retry predicate to `ParseError::BinderNeedsParens` — the only
error the tighter budget can produce that the looser one cannot — does **not**
fix it. A `BinderNeedsParens` that fails at *both* budgets (comparisons reject
binders at any budget) reproduces the same doubling:
`some A => … => A = all y: A | y = y` at k=20/24/26 → 0.33 s / 5.0 s / 20.5 s.
The repair has to bound retries structurally — memoize failures per
`(position, budget)`, or settle the `else` question by lookahead so no
speculative parse happens at all — which is a design call, not a no-fork detail.

Real-world exposure is currently low but not comfortable: across all 186,318
alloy4fun submission records the maximum `=>`/`implies` count in any single
submission is 29, and only 4 exceed 20 — a loose upper bound on any one chain,
so roughly an order of magnitude from the danger zone. The exponential needs
only a parse failure underneath the chain, which is what a corpus of student
submissions is full of.

## Implementation (2026-08-22)

`MAX_AST_PATH = 768` in `crates/als-syntax/src/parser.rs`, a **root-to-leaf
path** budget distinct from `MAX_EXPR_DEPTH` (which is unchanged and still
bounds the parser's own C-stack against a 1 MiB thread — two budgets, two
resources, one `TooDeep` diagnostic family). A unit is consumed by each nesting
level (`enter_depth`) and by each link of the two *iterative* chain sites: the
Pratt infix loop and `parse_postfix`'s dot/box-join loop. The second site
matters most — `A.r.r.r…` is the worst measured shape and the Pratt loop never
sees it. `parse_operand_at_depth` marks and restores the budget so every `?`
early return unwinds it, keeping the counter a path measure rather than a
whole-file total.

`ParseError::TooDeep` gained a `limit` field so the message names the budget
that actually fired instead of a hard-coded 256.

**Why a path budget rather than a per-chain cap:** nesting is separately capped
at 128 real `(`/`{` levels, so an adversarial file can place a full-length chain
at *every* level and reach ~128× any per-chain cap. Regression-tested
(`nesting_composed_with_chaining_is_bounded`): 100 nesting levels plus a
700-term chain — each individually under-bound — correctly exceeds the path
budget.

**Residual, per option (c):** an `Ast` built through the public API never passes
the parser, so `print`/`dump` remain unbounded there. Documented as
`print::MAX_SAFE_PRINT_PATH` with the measured printer/dumper crash points.
Closing it needs option (a), evaluated and rejected above.
