# Alloy 6 temporal semantics — pinned contract, wave 1 (mt-063)

**Status: wave 1 of N, in progress.** This document pins the reference
Alloy 6.2.0 jar's **temporal** behavior — the `var` surface, the `steps`
scope grammar, verdict semantics, and the Pardinus translation architecture
— as the authority Rung 6 (temporal solving, `docs/ROADMAP.md`) implements
from. Per this repo's method: **behavior is pinned by the oracle jar,
probed and recorded with evidence; a claim without a probe run or a source
citation is not pinned**, and an unresolved question is recorded as open
in ["Unpinned / next waves"](#unpinned--next-waves), never guessed.

This is wave 1 only. It pins (a) the temporal surface and discriminator,
(b) `steps` scope semantics exactly, (c) verdict semantics (minimality,
bound-relativity of UNSAT, the bounded/unbounded solver boundary), and
(d) the Pardinus translation architecture at reconnaissance depth (enough
to write a Rust architecture ADR from). It does **not** pin instance/trace
rendering or XML shape, enumeration operators (`next_state`, path
enumeration), REPL per-state evaluation beyond what
[alloy6-evaluator.md §4](alloy6-evaluator.md#4-the-temporal-edge-deferred-to-rung-6-d)
already noted, or counting under temporal scopes — all deferred to later
waves, listed explicitly below.

Provenance — same pinned oracle build as every other reference doc in this
directory: `oracle/org.alloytools.alloy.dist.jar` (6.2.0, build commit
`794226dd07b536fe35c5ca44b529417183cd629b`, ADR-0002). Probed on this
machine under **JDK 21** (Zulu, via the nix dev shell, the pinned harness
JDK — `/nix/var/nix/profiles/default/bin/nix ... develop -c`), platform
darwin/arm64 (confirmed by the jar's own `NativeCode` diagnostic log
lines). All facts below are tagged with a probe id (`T-NN`, jar-verified
2026-07-26) and/or a source/bytecode citation. Full harness, exact
commands, and verbatim jar output for every `T-NN` id:
`scratchpad/probe/mt063/NOTES.md` (gitignored; rerun with
`scratchpad/probe/mt063/rerun_all.sh` and `rerun_corpus.sh`).

The temporal solving engine bundled in the jar is **Pardinus** (a temporal
fork of Kodkod, package `kodkod.*` — same top-level package as static
Kodkod, distinguished by class names like `PardinusSolver`,
`TemporalTranslator`, `PardinusBounds`). Its classes are **not** present as
source in the jar or in `scratchpad/src794/` (which covers only the
Alloy-to-Kodkod translate/solution layer, `edu.mit.csail.sdg.*`) — pinned
here from `javap -p -c` bytecode disassembly of classes extracted from the
jar into `scratchpad/probe/mt063/jarextract/` (gitignored). Per
`PORTING_RULES.md`: reading jar bytecode to pin behavior is established
practice; no source or decompiled text appears verbatim anywhere in this
repo — `scratchpad/probe/mt063/TemporalProbe.java` is original code calling
the same public API the bytecode traces show, structured after
`scratchpad/probe/mt061/Probe.java`'s and `crates/als-conform/shim/
OracleShim.java`'s precedent (parse → `A4Options` → `TranslateAlloyToKodkod
.execute_command`).

---

## (a) Surface — `var`, the temporal operator set, the discriminator

**The full temporal operator set — 11 operators, confirmed by field
listing on the compiled `ExprUnary$Op`/`ExprBinary$Op` classes** (`javap
-p`, no source needed — a closed enum's field list is unambiguous):

- Unary (prefix): `after`, `always`, `eventually`, `before`,
  `historically`, `once`, and `'` (prime — `ExprUnary$Op.PRIME`, the same
  enum as the others, not special-cased).
- Binary (infix): `until`, `releases`, `since`, `triggered`.

This matches the task brief's operator list exactly, with `'`/`PRIME`
folded in as the 11th (it's an ordinary member of `ExprUnary$Op`
alongside `AFTER`/`ALWAYS`/etc., not a separate mechanism).

**The discriminator — what makes a command "temporal" — is
`CompUtil.isTemporalModel(Iterable<Sig> sigs, Command cmd)`**
(`scratchpad/src794/CompUtil.java:189-201`, cited by line, not copied):

```
for each reachable, non-builtin sig:
    if sig.isVariable != null: return true
    if any of its field decls has isVar != null: return true
return cmd.formula.hasTemporal()
```

`cmd.formula` is `globalFacts.and(commandBody)` — every reachable fact
conjoined with the command's own run-predicate/assertion body
(`scratchpad/src794/CompModule.java:2030`). So **a command is temporal iff
a `var` sig/field is reachable from it, *or* a temporal operator appears
anywhere in its facts-plus-body** — either condition alone suffices; they
are not required together. `Expr.hasTemporal()` itself
(`Expr.class`/`Expr$2.class` bytecode) requires the expression to already
be resolved without ambiguity/errors, then does a full-tree scan (not a
top-level check) via a cached `VisitQuery` that short-circuits on any of
the 11 operators above.

Both directions are jar-verified, not just source-read:

- **`var` alone, zero temporal operators** (probe **T-01**,
  `var sig A {}; fact { some A }; run {}`) → `isTemporalModel = true`.
- **A temporal operator alone, zero `var` anywhere** (probe **T-02**,
  `sig A {}; fact { always some A }; run {}`) → `isTemporalModel = true`
  as well — confirms the discriminator is a genuine *or*, not "only `var`
  counts."
- **Neither** (probe **T-03**, plain `sig A {}; fact { some A }`) →
  `isTemporalModel = false`, and attaching an explicit `for 3 steps` scope
  to that command is rejected: `ErrorSyntax("You cannot set a scope on
  \"steps\" in static models.")` (`ScopeComputer.java:479`/`:487`,
  jar-verified verbatim by T-03).

**A temporal operator in an otherwise-non-`var` model is legal and simply
makes that command temporal** (T-02) — there is no separate "temporal
operator used without `var`" error case; the two triggers are equally
valid ways into temporal mode, independently of each other.

**Every solved instance, temporal or not, is internally a
`TemporalInstance`.** Non-obvious bonus finding from T-03: even a fully
static command's solved `A4Solution` reports `isTemporal() == true`
(`A4Solution.java:951-953`, `eval.instance() instanceof TemporalInstance`)
and a well-formed `getTraceLength()==1`/`getLoopState()==0`, despite
`isTemporalModel` being `false` and the solver itself running in
non-temporal mode (`maxtrace==-1`, so `solver_opts.setRunTemporal(maxtrace
> 0)` was `false`). Pardinus wraps every result — even a genuinely static
one — in a (degenerate, 1-state, self-looping) `TemporalInstance` for API
uniformity. This is why
[alloy6-evaluator.md](alloy6-evaluator.md#0-the-evaluators-actual-code-path)
found `A4Solution.eval(Expr, int state)` always takes a state index, even
for ordinary non-temporal models (`state` is always `0` there) — now
explained: there is always a trace underneath, static models just get the
trivial length-1 case.

---

## (b) `steps` scopes, exactly

**Where it lives.** `Command`'s public fields are `minprefix`/`maxprefix`
(`int`, `-1` sentinel for "not given" — `Command.class` bytecode; there is
no field literally named `steps`, it's parser sugar over these two ints).
`ScopeComputer` resolves them into the `A4Solution`-level `mintrace`/
`maxtrace` (`ScopeComputer.java:110/115` field defaults: `maxtrace=10`,
`mintrace=1`; `:474-493` the resolution logic, cited by line below).

**Default, when `steps` is absent entirely on a temporal command**:
`mintrace = 1`, `maxtrace = 10` — the search range is `[1, 10]`, i.e. up to
10 states. Jar-verified: **T-01, T-02, T-04** (all `var sig A {};
fact{some A}; run {}` variants with no `steps` clause) each solved with
`sol.getMinTrace()==1, sol.getMaxTrace()==10`; independently reconfirmed by
real corpus content — `trash.als`'s `check deleteAll`/`Exercise1..4`
(no `steps` clause) all resolve to the same `[1,10]` range (see §(e)).

**A bare `for N steps` means "search range `[1, N]`", NOT "exactly N
states"** — the single most load-bearing, non-obvious fact in this
section. Predicted from source before running (`ScopeComputer.java:
475-482`: `tracelength = cmd.maxprefix` unless `<1` then default `10`;
`:484-492`: `tracelength = cmd.minprefix` unless `> maxprefix` (clamp) or
`<1` (default `1`) — a bare `for N steps` leaves `minprefix` at its `-1`
sentinel, so `mintrace` defaults to `1`, never `N`). Jar-verified:
**T-06** (`for 3 steps` → `Command.toString()` renders bare `"for 3
steps"` with `minprefix=-1` still unset at the `Command` level, but the
*solved* `A4Solution` has `getMinTrace()==1, getMaxTrace()==3`).
Independently reconfirmed by corpus content: `trash.als`'s `check
restoreAfterDelete for 10 steps` resolves to `getMinTrace()==1,
getMaxTrace()==10`, same shape.

**An explicit range `for N..M steps`** sets `minprefix=N, maxprefix=M`
directly, round-tripping unchanged into `mintrace=N, maxtrace=M`.
Jar-verified: **T-05** (`for 1..4 steps` → `getMinTrace()==1,
getMaxTrace()==4`).

**`exactly` on `steps` is legal** — not something guessable from
`ScopeComputer.java` alone (that file only sees the already-resolved
`minprefix`/`maxprefix` ints, not the grammar production that produces
them; genuinely an open question until probed). **T-07**: `for exactly 3
steps` parses, and `Command.toString()` renders it back as `"for 3..3
steps"` — i.e. `exactly N` desugars to `minprefix=maxprefix=N`, identical
to writing `N..N` directly. The solved trace is then forced to exactly
that length (`getTraceLength()==3` in T-07).

**Open-ended ranges (`for N.. steps`, no upper bound) are legal *only*
when `N == 1`.** **T-08a**: `for 3.. steps` is rejected at parse time —
`ErrorSyntax("Unbounded time scope must start at 1.")`. **T-08b**: `for
1.. steps` parses fine, and sets `maxprefix = Integer.MAX_VALUE`
(confirmed by inspecting the `Command` field directly, and by
`Command.toString()`'s bytecode, which special-cases `maxprefix ==
Integer.MAX_VALUE` to skip printing a number — `"for 1.. steps"`, not
`"for 1..2147483647 steps"`). This exact syntax appears in the real corpus
(`trash.als`: `check restoreAfterDelete for 1.. steps`, `check
restoreIsPossibleBeforeEmpty for 3 but 1.. steps` — see §(e)), so it is
live, in-scope syntax mettle's parser must accept (and per the task brief,
already does).

**`Integer.MAX_VALUE` is exactly the unbounded-solving trigger.**
`A4Solution.java:409`: `solver_opts.setRunUnbounded(maxtrace ==
Integer.MAX_VALUE)`. §(c) below covers what actually happens when that
flag is set under the default (bounded) solver.

---

## (c) Verdict semantics

**The solver is a bounded, incremental, minimal-length search — confirmed
by full bytecode disassembly of `TemporalPardinusSolver.solve(Formula,
PardinusBounds)`**, not inferred from behavior alone (see §(d) for the
exact decompiled control flow). In prose: for `k = mintrace, mintrace+1,
..., maxtrace`, expand the bounds to trace length `k`
(`TemporalTranslator.expand(k)`), translate+solve at that length, and
**return immediately on the first SAT** — never trying a longer length
once one succeeds. If no `k` up to `maxtrace` is satisfiable, the result is
UNSAT.

This single mechanism explains every verdict-semantics finding below:

- **The returned trace is always the *minimal* satisfying length, not the
  maximum available.** **T-09**: a model satisfiable at every length
  `>= 2` up to the default max of 10 (`no B; after always some B`) returns
  `getTraceLength()==2`, not `10`. **T-10b**: a `check` satisfiable at
  length 3 but bounded at `for 4 steps` (so both 3 and 4 would fit) still
  returns `getTraceLength()==3`, not `4` — a second, independent
  confirmation with a `check` command rather than a `run`.
- **UNSAT means "no counterexample/instance within the given `steps`
  bound" — not "the assertion holds forever."** Raising the bound can flip
  the verdict. **T-10b**, cleanly (no boundary quirks): the same `check
  NeverB` is UNSAT `for 2 steps` and SAT `for 3 steps` (and `for 4 steps`)
  once the bound is large enough to reach the actual violating state. This
  is the honest, bound-relative reading of a temporal `check`'s UNSAT that
  the task brief asked to pin explicitly — it is **not** "verified true",
  it is "no counterexample found up to this many states."
- **Every SAT temporal instance observed is a lasso (finite prefix + a
  back-edge/loop), never a "genuinely infinite, non-repeating" trace** —
  `getLoopState()` returned a valid in-range state index (`0 <=
  getLoopState() < getTraceLength()`) in every single SAT probe in this
  wave (T-01, T-02, T-04 through T-12's SAT cells, all corpus SAT
  commands). This matches the architecture: `TemporalTranslator`'s `LOOP`
  relation is a mandatory part of the encoding (§(d)), so a satisfying
  assignment always includes a loop target by construction — there is no
  code path that produces a trace without one.
- **`expect` interplay is unchanged under temporal commands.** **T-12**:
  `TranslateAlloyToKodkod.execute_command` returns the actual solved
  verdict regardless of `cmd.expects`, for both a matching and a
  mismatching expectation on a temporal `run` — no special-casing at this
  layer, consistent with `expects`-vs-actual comparison living in a higher
  (CLI/GUI) layer, same as already established for static commands
  elsewhere in this repo's pinned docs.
- **The default engine is the bounded SAT one; the unbounded (Electrod)
  path is a structurally separate solver that the default configuration
  can never silently fall into.** `TemporalPardinusSolver.solve` itself
  asserts `!options.unbounded()` on entry (bytecode: `getstatic
  $assertionsDisabled; ...; new AssertionError` guard) — it is *only* ever
  the bounded path. **T-08b**: attempting to solve a `maxtrace ==
  Integer.MAX_VALUE` command with the default `sat4j` solver throws
  immediately: `ErrorAPI("Bounded engines do not support complete model
  checking.")` — before any electrod/unbounded machinery is reached at
  all. Reconfirmed against real corpus content, not just a hand-built
  fixture: `trash.als`'s two `1.. steps` commands hit the identical error
  under the default solver (§(e)). The jar does bundle a native `electrod`
  binary per platform (`native/{darwin,linux,windows}/{amd64,arm64}/
  electrod{,.exe}` — confirmed present in the jar's file listing for this
  machine's platform, darwin/arm64), so the unbounded path is plausibly
  reachable via a different, deliberately-selected solver — but the
  correct `SATFactory` name to select it was **not found** this pass
  (`"electrod"`, `"ElectrodNuXmv"`, `"ElectrodNuSMV"`, `"nuXmv"`, `"NuXmv"`
  all rejected as unknown by `SATFactory.find`). This is genuinely
  Rung-6-out-of-scope (mettle's North Star is the bounded solving path
  Alloy uses by default); recorded honestly as unresolved, not guessed
  — see "Unpinned / next waves".

### A genuine jar bug, pinned honestly (not mettle's to silently replicate or silently "fix" without a ledger decision)

**Any `check` command whose resolved `maxtrace == 1` throws a
`NullPointerException` (wrapped as `ErrorFatal("Unknown exception
occurred: ...")`) instead of returning a clean verdict.** Verbatim:

```
edu.mit.csail.sdg.alloy4.ErrorFatal: Unknown exception occurred: java.lang.NullPointerException: Cannot invoke "kodkod.engine.fol2sat.Translation$Whole.cnf()" because "translation" is null
```

Reproduced twice with unrelated fact bodies — **T-10a** (`fact { no Flag;
always (no Flag => after some Flag) }`, `check ... for 1 steps`) and a
minimal isolation with no `after` in the fact at all (`fact { no Flag }`,
same `check ... for 1 steps`) — so the bug is general to `check` +
`maxtrace==1`, not specific to any particular formula shape. **T-11**
isolates it to `check` specifically: the identical `maxtrace==1` bound on
a plain `run` command (`run {} for 1 steps`, `run {} for exactly 1 steps`)
solves cleanly with no error. Not chased into Pardinus internals to find
the root cause (a `check` negates the assertion and solves that — the bug
is presumably somewhere in how that negated-formula path handles a
`Translation$Whole` that comes back `trivial()`/degenerate at the
single-state bound) — recorded as observed jar behavior, exact repro
given, mechanism not claimed. This is the same category of finding as this
repo's other pinned oracle quirks (the dead `-y` flag, the
entry-point-dependent overflow default — see the `mettle-oracle-gotchas`
memory note) and should be treated the same way: **Rung 6 must decide,
with a Ledger entry, whether mettle reproduces this exact failure at
`check ... for 1 steps` or diverges (and if it diverges, that divergence
belongs in `LIMITATIONS.md`)** — not silently "fixed" by an agent without
that decision being made explicitly.

---

## (d) Translation architecture reconnaissance

Depth target here is "enough to write a Rust architecture ADR from this
description without re-reading the bytecode" — the task's own bar. Read
via `javap -p -c` on classes extracted from the jar
(`scratchpad/probe/mt063/jarextract/`), never source-copied.

**Key classes and responsibilities:**

| Class | Responsibility |
|---|---|
| `kodkod.engine.ltl2fol.TemporalTranslator` | The LTL→FOL reduction. Holds `STATE, FIRST, LAST, PREFIX, LOOP` relations (plus `TRACE`, and unroll-support relations `LAST_, UNROLL_MAP, LEVEL, L_FIRST, L_LAST, L_PREFIX`). `translate()` turns the temporal `Formula` into a plain (non-temporal) `Formula` over these relations; `expand(int k)` produces a `PardinusBounds` sized for trace length `k`. |
| `kodkod.instance.PardinusBounds` (`extends Bounds`) | Bounds that additionally track which relations are "all"/"symbolic"/targeted (`relations_all`, `relations_symb`, `targets`, `weights` — the last two for target-oriented solving, a different Pardinus feature not otherwise touched by this wave). `hasVarRelations()` exists to ask whether any bound relation is `var`-backed. |
| `kodkod.engine.TemporalPardinusSolver` | The bounded temporal solver. `solve(Formula, PardinusBounds)` runs the incremental `for k in [mintrace,maxtrace]` search described in §(c), returning on first SAT. Asserts `!unbounded()` on entry — structurally only the bounded path. |
| `kodkod.engine.PardinusSolver` | The outer solver `A4Solution` actually constructs (`new PardinusSolver(solver_opts)`, `A4Solution.java:440`) — dispatches to a `TemporalSolver` or a plain static `AbstractSolver` depending on `options.temporal()`, uniformly for every command (temporal or not — consistent with the "every instance is a `TemporalInstance`" finding in §(a)). |
| `kodkod.instance.TemporalInstance` (`extends Instance`) | The result shape: `states: List<Instance>`, `loop: int` (back-edge target index), `unrolls: int`. `prefixLength()`, `state(int)`, `normalizedIndex(int)` (wraps an out-of-range logical index back into `[0, prefixLength)` through the loop — same modulo-through-the-loop logic independently visible in `A4Solution.toString(int state)`, `A4Solution.java:1794-1795`). |
| `kodkod.engine.config.TemporalOptions` (interface, extends `PardinusOptions`) | `setRunTemporal(boolean)`, `min/maxTraceLength()` + setters — exactly the options `A4Solution.java:405-409` wires from `mintrace`/`maxtrace`. |
| `kodkod.engine.DecomposedPardinusSolver`, `PardinusBounds.splitAtTemporal` | Plumbing for the **decompose** strategy (`A4Options.decompose_mode`, parallel/hybrid solving) — confirmed (`A4Solution.java:1622-1626`) to run only when `solver.options().decomposed()`; irrelevant to the default single-threaded path every probe in this document used. Not chased further — flagged as deliberately not chased. |

**Static-vs-variable relation partitioning** is not a separate step in the
default path — it falls out of `expand(k)` itself. A relation backed by a
`var` sig/field (`Sig.isVariable != null` / `Decl.isVar != null`,
`BoundsComputer.java` — cited generally, not line-by-line, at
:156,178,194,206,225,241,245,262,270,417-418,425,435,448,450,473,477,479)
gets unrolled across the `k` states; a relation backed by a non-`var`
sig/field stays one time-independent copy shared by every state. `int`/
`Int`/`String`/`seq` are never `var`-declared (builtin, `isVariable ==
null` always) — **so integers and strings are rigid across all states by
construction, not by a special case**. This specific claim is
source-cited only, not independently probed this wave (see "Unpinned /
next waves") — the general mechanism (T-01 through T-12 all solve
correctly with `Int`-typed facts/expressions coexisting with `var` sigs)
is consistent with it, but no probe isolated "does `Int` differ between
two states" directly.

**Symmetry breaking under time**
(`scratchpad/src794/SymmetryBreaker.java:207-259`, `generateSBP`): when
the bounds contain `TemporalTranslator.STATE`, the lex-leader SBP
generator iterates the state atoms and re-applies the *same*
permutation-ordering constraint **independently at every state** (an
outer loop around the per-relation constraint logic) — symmetry is broken
per-state, not once across the whole flattened unrolled trace. Separately,
explicitly: `if (r.isSkolem() && options.temporal()) continue;`
(`:231-232`) — **skolem relations are unconditionally excluded from
symmetry-breaking-predicate generation whenever running in temporal
mode.** Source-cited, not independently probed (a probe would need to
inspect the generated SBP's clause structure, out of reach without
`recordKodkod`-level introspection this wave didn't build) — but the
citation is a specific, unambiguous `if` gate, not an inference.

**Skolemization is switched off entirely under any temporal operator.**
`scratchpad/src794/Skolemizer.java:494-526`,
`visit(BinaryTempFormula)`/`visit(UnaryTempFormula)`, both carrying the
comment `// [HASLab] temporal formulas, cannot skolemize`: on entry,
`skolemDepth` is forced to `-1` for the entire subtree under the temporal
operator (restored after descending). No quantifier nested inside
`always`/`eventually`/`until`/etc. is ever skolemized, regardless of the
model's configured skolem depth. This is the same family of finding as
this repo's prior `core(lower): block skolemization where Kodkod does`
(mt-055) — confirmed here to extend specifically to the temporal case.

**Where `'` (prime) lands.** `PRIME` is an ordinary member of
`ExprUnary$Op` at the Alloy-AST level and of `kodkod.ast.operator.
TemporalOperator` at the Kodkod-AST level (both confirmed by field
listing — same enum family as `always`/`eventually`/etc., no separate
mechanism). The structural claim that prime ultimately compiles to a
`PREFIX` (successor-relation) reference in the `expand(k)` encoding is
supported by `PREFIX`'s presence and naming in `TemporalTranslator`, but
tracing the exact opcode sequence that folds prime into it was not chased
byte-for-byte — flagged as not chased (see "Unpinned / next waves"; the
architectural picture above should already be enough to design mettle's
own encoding without needing that specific trace).

**Deliberately not chased this wave** (flagged honestly, not silently
skipped): the exact bytecode of `TemporalTranslator.expand(int)`/
`translate()` themselves (confirmed their existence, signatures, and the
relations they operate over; did not disassemble their bodies — the
external behavior (§(c)'s solve loop, minimality, lasso shape) is already
independently confirmed by probes, and PORTING_RULES's directive is to pin
*behavior*, not replicate internal structure); `PardinusBounds`'s
target-oriented (`targets`/`weights`) machinery, unrelated to plain
temporal solving; `TemporalBoundsExpander`'s `extend(...)` overloads
(incremental bounds extension across `next()`/enumeration calls — likely
relevant to a future wave on enumeration, not verdict semantics); the
exact SAT-solver-internal loop-placement choice among multiple valid
options (T-07 placed the loop at the last state for an unconstrained
model — whether that's deterministic given fixed solver/symmetry settings
or coincidental to `sat4j`'s search order was not tested by re-running
with a different seed/solver).

---

## (e) Harness check

**`OracleShim` (`crates/als-conform/shim/OracleShim.java`) can already run
the corpus temporal files headlessly, unmodified.** It drives every
command through the identical `A4Options` → `TranslateAlloyToKodkod
.execute_command` entry point this probe wave used, and that entry point
has no temporal/static branch at the call site — `ScopeComputer.compute`
handles `isTemporalModel`/`steps` resolution transparently underneath.
`OracleShim`'s JSON output doesn't currently expose
`getMinTrace`/`getMaxTrace`/`getTraceLength`/`getLoopState` (only
`verdict`/`instance_count`), so it can't be used to observe trace-length/
loop-state facts directly — a future wave wanting that would need a small,
additive JSON field (not made this wave; shim is production code, out of
scope for this probe task per its brief). No shim tweak was needed to get
correct SAT/UNSAT verdicts for all four corpus files.

**Corpus verdicts** (`symmetry=20, noOverflow=false, solver=sat4j`, this
repo's standing defaults; full per-command wall times in
`scratchpad/probe/mt063/NOTES.md`):

- **`buffer.als`** (5 cmds, ~118s total): `run{}`→SAT,
  `everyReceivedValueWasSent` (check for 4)→UNSAT (12.9s),
  `orderIsPreserved` (check for 3)→UNSAT (89.9s — the slowest single
  command probed this wave), `receiveWeakFairness`→SAT,
  `everySentValueWillBeReceived` (check for 3)→UNSAT (13.0s).
- **`leader.als`** (4 cmds, ~4.3s): `run{}`→SAT, `example`→SAT,
  `safety` (check for 3 but 15 steps)→UNSAT, `liveness` (check for
  3)→**SAT**.
- **`leader_events.als`** (4 cmds, ~7.3s): same shape as `leader.als`
  except `liveness`→**UNSAT** — a real semantic divergence between the two
  near-identical models (one has a static `elected` sig, the other a
  `var sig elected`), not a probe artifact; not investigated further
  (corpus-content question, not a jar-behavior question).
- **`trash.als`** (9 cmds, ~2.9s): 7 clean SAT/UNSAT verdicts plus the two
  `1.. steps` commands both hitting `ErrorAPI("Bounded engines do not
  support complete model checking.")` under the default solver — real
  corpus content reconfirming T-08b, not just a hand-built fixture.

---

## Probe evidence table

Full commands, predictions-before-run, and verbatim jar output for every
id: `scratchpad/probe/mt063/NOTES.md`. Rerun:
`scratchpad/probe/mt063/rerun_all.sh` (fixtures) and `rerun_corpus.sh`
(corpus files — `buffer.als` alone is ~2 minutes).

| id | Fixture | What it pins |
|---|---|---|
| T-01 | `VarNoOp.als` | `var` sig alone → `isTemporalModel=true`; default steps `[1,10]` |
| T-02 | `OpNoVar.als` | Temporal operator alone (no `var`) → `isTemporalModel=true` |
| T-03 | `Neither.als` | Neither → `isTemporalModel=false`; `steps` on a static command is `ErrorSyntax`; bonus: `isTemporal()==true` on a fully static solve |
| T-04 | `DefaultSteps.als` | Default steps `mintrace=1, maxtrace=10`, reconfirmed |
| T-05 | `RangeSteps.als` | `for 1..4 steps` → `minprefix=1, maxprefix=4`, round-trips into solved trace bounds |
| T-06 | `BareSteps.als` | `for 3 steps` → range `[1,3]`, NOT exactly 3 |
| T-07 | `ExactlySteps.als` | `for exactly 3 steps` is legal, desugars to `3..3`, forces trace length exactly 3 |
| T-08a | `UnboundedSteps.als` | `for 3.. steps` → `ErrorSyntax("Unbounded time scope must start at 1.")` |
| T-08b | `UnboundedSteps1.als` | `for 1.. steps` → `maxprefix=Integer.MAX_VALUE`; default (bounded) solver → `ErrorAPI("Bounded engines do not support complete model checking.")` |
| T-09 | `MinLen.als` | Solver returns the *minimal* satisfying trace length, not the max available |
| T-10a | `CounterexampleAtLength.als`, `TrivialLen1.als` | `check ... for 1 steps` → jar bug: `NullPointerException`/`ErrorFatal`, reproduced with two unrelated fact shapes |
| T-10b | `CounterexampleAtLength2.als` | Clean UNSAT(2)→SAT(3)→SAT-still-minimal(4) — bound-relativity of UNSAT, and a second minimality confirmation, with no boundary bug |
| T-11 | `RunLen1.als` | `run ... for 1 steps` (not `check`) solves cleanly — isolates T-10a's bug to `check` specifically |
| T-12 | `ExpectTemporal.als` | `expect` mismatch on a temporal `run` doesn't throw at the `execute_command` layer — same as static commands |

---

## Unpinned / next waves

Honest gaps, not silently glossed over:

- **Instance/trace rendering and XML shape for temporal instances.**
  `A4SolutionWriter`/`A4SolutionReader`'s handling of a multi-state
  `TemporalInstance` (how `loop`/`unrolls`/per-state tuples serialize to
  XML) was not examined at all this wave — needed before mettle can render
  a temporal counterexample/instance the way Sterling does.
- **Enumeration operators under time** (`next()`'s temporal variants —
  `A4Solution`'s constructor comment at `:448-449` mentions "-3 standard
  next, -2 next path, -1 next config, >=0 fork at state" — none of these
  were probed). `TemporalBoundsExpander.extend(...)`'s role in incremental
  enumeration was identified structurally but not exercised.
- **REPL per-state evaluation**, beyond what
  [alloy6-evaluator.md §4](alloy6-evaluator.md#4-the-temporal-edge-deferred-to-rung-6-d)
  already found (evaluating the same expression at different `state`
  values gives fact-consistent, different answers) — how `OurConsole
  .current`/`setCurrentState(int)` gets driven as a user steps through a
  trace in the GUI, and what `mintrace`/`maxtrace`/loop-state bounds mean
  for *valid* `state` arguments to `eval`, remain open.
- **Counting under temporal scopes** — how the conformance-scorecard
  instance-counting gauge (ADR referenced from `docs/adr/`) should treat a
  `steps` range (count per-length? count only the minimal length? count
  across enumeration?) is unaddressed; this wave only ever looked at the
  *first* solve, never enumerated multiple temporal instances.
- **The correct solver name to actually invoke the bundled `electrod`
  binary and observe genuine unbounded solving.** Five plausible
  `SATFactory` names were tried and rejected (`electrod`, `ElectrodNuXmv`,
  `ElectrodNuSMV`, `nuXmv`, `NuXmv`); the actual name (if directly
  reachable through `A4Options.solver` at all, rather than only through a
  GUI preference/menu path not modeled by `A4Options`) is unresolved.
  Explicitly Rung-6-out-of-scope per this repo's North Star (mettle
  targets the default bounded solving path first) — recorded as open, not
  guessed.
- **The `check ... for 1 steps` `NullPointerException` jar bug's root
  cause inside Pardinus** — the exact repro is pinned (T-10a/T-11), the
  internal mechanism is not. A Ledger decision (reproduce the failure vs.
  diverge, with the divergence recorded in `LIMITATIONS.md`) is owed
  before Rung 6 implements `check` verdict handling at trace-length-1
  bounds.
- **Integers/Strings-stay-rigid**, and **the SB-per-state / skolem-skip
  findings in §(d)**, are source-cited (specific, unambiguous citations)
  but not independently probe-confirmed by inspecting generated SAT
  clauses or a live cross-state `Int` comparison. Low risk (the citations
  are specific `if`-gates, not inferences from surrounding code shape) but
  flagged per this repo's "probe or cite, never both-absent" standard.
- **The exact bytecode of `TemporalTranslator.expand`/`translate`** was
  not disassembled body-for-body (see "Deliberately not chased this wave"
  in §(d)) — the external behavior it produces is independently pinned by
  probes, but a future wave wanting the literal encoding shape (e.g. to
  cross-check a specific edge case in mettle's own encoder) would need to
  go back to that bytecode.
- **This document does not yet appear in `docs/README.md`'s reference
  index** — the task's constraints for this probe pass excluded editing
  any `docs/` file other than this new one; linking it in
  `docs/README.md` (next to `alloy6-evaluator.md`/`alloy6-translation.md`)
  is a small follow-up the tech lead should do when merging this wave.
