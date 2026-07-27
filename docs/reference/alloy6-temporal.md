# Alloy 6 temporal semantics — pinned contract, waves 1–3 (mt-064 … mt-076)

**Status: three waves complete** — wave 2's frame below stands, and the
mt-069 closing wave (§(m)) plus the mt-076 wave (§(g)/§(i): enumeration
`next`/`fork` parity, the configuration-lock correction) closed the
enumeration-counting gaps wave 2 left open. This document pins the reference
Alloy 6.2.0 jar's **temporal** behavior — the `var` surface, the `steps`
scope grammar, verdict semantics, the Pardinus translation architecture,
trace/XML rendering, enumeration operators, the evaluator's per-state
story, and counting under temporal scopes — as the authority Rung 6
(temporal solving, `docs/ROADMAP.md`) implements from. Per this repo's
method: **behavior is pinned by the oracle jar, probed and recorded with
evidence; a claim without a probe run or a source citation is not
pinned**, and an unresolved question is recorded as open in
["Unpinned / next waves"](#unpinned--next-waves), never guessed.

**Wave 1** (§(a)-(e) below) pinned the temporal surface and discriminator,
`steps` scope semantics exactly, verdict semantics (minimality,
bound-relativity of UNSAT, the bounded/unbounded solver boundary), and the
Pardinus translation architecture at reconnaissance depth. **Wave 2**
(§(f)-(j) below) closes most of what wave 1 deferred: (f) trace instance
rendering and the temporal XML shape, (g) the enumeration operators
(`next()`'s `fork(p)` variants and their GUI wiring), (h) the evaluator's
per-state story (state validity bounds, temporal operators as direct
eval input — closing
[alloy6-evaluator.md §4](alloy6-evaluator.md#4-the-temporal-edge-deferred-to-rung-6-d)'s
deferred questions), (i) counting under temporal scopes (reproducing a
real corpus count baseline live and pinning the enumeration operator it
implies), and (j) two wave-1 loose ends (the electrod solver id,
`minprefix=-1`-vs-explicit-`1` equivalence). What remains open after both
waves is listed in "Unpinned / next waves" — it is materially smaller than
after wave 1.

Provenance — same pinned oracle build as every other reference doc in this
directory: `oracle/org.alloytools.alloy.dist.jar` (6.2.0, build commit
`794226dd07b536fe35c5ca44b529417183cd629b`, ADR-0002). Probed on this
machine under **JDK 21** (Zulu, via the nix dev shell, the pinned harness
JDK — `/nix/var/nix/profiles/default/bin/nix ... develop -c`), platform
darwin/arm64 (confirmed by the jar's own `NativeCode` diagnostic log
lines). All facts below are tagged with a probe id (`T-NN`, wave 1 ids
jar-verified 2026-07-26, wave 2 ids `T-13`-`T-28` jar-verified 2026-07-26)
and/or a source/bytecode citation. Full harness, exact commands, and
verbatim jar output: wave 1 — `scratchpad/probe/mt063/NOTES.md` (gitignored;
rerun with `scratchpad/probe/mt063/rerun_all.sh` and `rerun_corpus.sh`);
wave 2 — `scratchpad/probe/mt064/NOTES.md` (gitignored; rerun with
`scratchpad/probe/mt064/rerun_all.sh`).

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

## Wave 2 (mt-064)

Harness, fixtures, predictions-before-run, and full verbatim jar output for
every `T-13`-`T-28` id below: `scratchpad/probe/mt064/NOTES.md` (gitignored;
rerun with `scratchpad/probe/mt064/rerun_all.sh`, plus two cheap one-off
commands for T-26/T-27 documented inline there). Harness code:
`scratchpad/probe/mt064/TraceProbe.java` (new — `trace`/`enumnext`/`fork`/
`evalstates` modes against the live, in-process `A4Solution`, the same
`A4Options`/`TranslateAlloyToKodkod` entry point as mt063's `TemporalProbe`),
`scratchpad/probe/mt064/EvalProbe.java` (an unmodified copy of mt061's
`Probe.java`, class renamed only — the pinned GUI evaluator XML-round-trip
path, reused to cross-check the temporal eval findings against the *real*
console path, not just direct in-process eval), `ListSolvers.java` (new —
enumerates `SATFactory.getAllSolvers()` rather than guessing solver-id
strings).

## (f) Trace instance rendering + XML

**One `<instance>` XML element per trace state, not one element for the
whole trace.** Jar-verified (**T-13**, a forced 3-state trace; **T-14**, the
static/1-state contrast): `A4Solution.writeXML` emits `tracelength`
independent `<instance ...>` blocks inside the single `<alloy>` root, each
carrying the *same* file-level metadata attributes (`bitwidth`, `maxseq`,
`mintrace`, `maxtrace`, `command`, `filename`, `tracelength`) — only the
per-`<sig>` `<atom>` content of `var`-marked sigs (`<sig ... var="yes">`)
differs between the blocks. Non-`var` sigs (including all four builtins —
`univ`, `Int`, `seq/Int`, `String` — and any non-`var` user sig) are
re-emitted, byte-identical, in every block; there is no factoring-out of
rigid content across states in the XML (nor in `A4Solution.toString(int
state)`'s equivalent text rendering — see below).

**The loop is encoded as `looplength`, not as a loop-state index.** There is
no `loop="N"` attribute. Instead every `<instance>` carries `looplength="K"`
where **`K = tracelength - loopState`** (T-13: `tracelength="3"
looplength="1"` for a trace with `getLoopState()==2`; T-14: `tracelength="1"
looplength="1"` for the degenerate static case, `getLoopState()==0`). A
reader must recover the loop state as `tracelength - looplength`. A static
(non-temporal) command's XML has this exact same shape, degenerated to a
single `<instance>` block (`tracelength="1" looplength="1"`) — consistent
with wave 1 §(a)'s "every solved instance is internally a `TemporalInstance`"
finding, and with `mintrace`/`maxtrace`'s `-1` static sentinel being written
into the XML verbatim rather than normalized away (T-14).

**The plain-text rendering (`A4Solution.toString(int state)`,
`scratchpad/src794/A4Solution.java:1767-1816`) is source-pinned exactly, and
now also jar-verified (T-13/T-14) to match its own source precisely** — no
surprises needed probing for once, since the method body is plain,
readable Java: called with `state < 0` on a `TemporalInstance`, it emits a
`"---Trace---"` header followed by one `"------State N-------"` (or
`"------State N (loop)-------"` for the loop state) block per state, each
listing every sig (`label=<eval>`) and field (`label<:field=<eval>`) at
that state, plus every skolem. Called with `state >= 0`, it clamps/wraps
`state` via the identical `Math.max(0, state)` / loop-modulo logic this
wave's §(h) independently reconfirms for `eval()` itself (see below) and
renders only that one state's block (prefixed `"---Instance---"` for a
non-temporal solve, no prefix for a temporal one). This is the string
`mettle exec`'s temporal rendering will be judged against by inspection
(the conformance scorecard itself doesn't diff instance text — see
[alloy6-evaluator.md §5](alloy6-evaluator.md#5-design-implications-for-mettles-repl-mt-062)'s
same point about tuple order — but a human running `mettle exec` side by
side with the reference GUI will compare this shape).

Not re-verified this wave: the `<source filename=... content=...>` /
top-level `<instance filename="...">`-for-reparse protocol
[alloy6-evaluator.md §0](alloy6-evaluator.md#0-the-evaluators-actual-code-path)
already pinned for the non-temporal case — T-13/T-14 both passed
`sourceFiles=null` to `writeXML` to keep the harness's own stdout minimal,
so those elements don't appear in the captured XML here. No reason to
expect they interact differently with a multi-`<instance>` temporal file
(the reparse logic wave 1's evaluator doc found just takes the *first*
`<instance>` element's `filename` attribute, which is present and identical
in every block per the finding above), but this specific combination
wasn't independently re-run with `sourceFiles` populated.

## (g) Enumeration operators

**The dispatch, source-pinned exactly**
(`scratchpad/src794/A4Solution.java:1829-1855`, doc comment at `:448-449`):
`A4Solution.next()` is exactly `fork(-3)`. `fork(p)` requires
`isIncremental()` (the solver used `solveAll`, true for this repo's standing
default `sat4j`) and dispatches on `p`: `-1` → `kEnumerator.nextC()` ("next
config"), `-2` → `kEnumerator.nextP()` ("next path"), `p >= 0` →
`kEnumerator.nextS(p, 1, rels)` ("fork at state `p`", `rels` = the model's
`var`-marked relations), anything else (including the canonical `-3`) →
`kEnumerator.next()` ("standard next").

**The GUI wiring, bytecode-traced** (`javap -p -c`,
`edu/mit/csail/sdg/alloy4viz/VizGUI.class`, extracted in mt061's
`jarextract/` and reused here — five toolbar buttons, each calling the
enumerator `Computer`'s `compute(new String[]{xmlFileName, "<p>"})`, the
same two-element-`Object[]`/`Computer` protocol
[alloy6-evaluator.md §0](alloy6-evaluator.md#0-the-evaluators-actual-code-path)
pinned for the *separate* evaluator `Computer`):

| Toolbar label | Tooltip | Method | `p` sent |
|---|---|---|---|
| "New" | "Show a new solution" | `doNext()` | `"-3"` |
| "New Config" | "Show a new configuration" | `doConfig()` | `"-1"` |
| "New Trace" | "Show a new trace" | `doPath()` | `"-2"` |
| "New Init" | "Show a new initial state" | `doInit()` | `"0"` |
| "New Fork" | "Show a new fork" | `doFork()` | `current + 1` (`current` = `VizGUI`'s currently-displayed-state field) |

So **"New Init" is `fork(0)` and "New Fork" is `fork(current+1)`** — both
route through the identical `p >= 0` dispatch branch; only the state index
differs. (`doNavLeft()`/`doNavRight()`, the `<`/`>` state-stepper arrows, are
an unrelated, solver-free mechanism — see §(h).)

**What `fork(p)` for `p >= 0` operationally holds fixed — settled
empirically, not from the bytecode alone** (a `TemporalPardinusSolver
$SolutionIterator` lambda predicate filtering on `IterationStep.start`
*suggested* a prefix-holding mechanism exists, but reading its exact cut
point off raw stack-order bytecode is exactly the kind of inference this
repo's method distrusts without a probe to confirm the direction — see
`scratchpad/probe/mt064/NOTES.md`'s T-20 write-up for the full reasoning).
**T-20/T-21** (comparing `fork(p)`'s `toString(-1)` state-blocks against the
original, state by state, on two different fixtures): **`fork(p)` holds
states `0..p-1` byte-identical to the original and forces state `p` onward
to a new value.** `fork(0)` ("New Init") therefore changes state 0 itself —
matching its "new initial state" label. `fork(current+1)` ("New Fork") holds
every state the user has already looked at (`0..current`) fixed and only
diverges strictly after it — matching "a new fork" (branching off from
where you currently are). `fork(-3)`/`fork(-2)` ("next"/"next path") held
nothing fixed in both fixtures tested (state 0 already differs). `fork(-1)`
("next config") behaved consistently with "config = the assignment of the
model's *static* (non-`var`) relations" (matching a `!isVariable()` filter
independently visible in the same bytecode) but its *failure* mode when no
alternate config exists differed across the two fixtures tested — UNSAT in
one, the byte-identical original solution returned again in the other (see
"Unpinned" below; does not affect the `p >= 0` prefix-holding pin, which is
consistent and clean across both fixtures).

**Plain `next()`/`fork(-3)` gives genuinely distinct successive traces**
(**T-16**, six pairwise-distinct traces from one starting solution) and
**is not confined to the first-found (minimal) trace length — it exhausts
the raw solution space at each length before advancing to the next length
in the command's `[mintrace,maxtrace]` steps range** (**T-19**, the wave's
single most load-bearing enumeration finding: a `1..3 steps` command's
`next()` sequence gives both raw length-2 solutions first, then genuinely
advances to length-3 solutions, never reporting UNSAT prematurely just
because the minimal length was exhausted). This directly explains §(i)'s
counting behavior below. (T-17's `MinLen.als` cell *seemed* to contradict
this — only one solution before UNSAT, even at `symmetry=0` — but T-19's
cleaner fixture shows this was a `MinLen.als`-specific anomaly, not
evidence that enumeration is length-confined in general; see "Unpinned"
below.)

### The mt-076 probe wave — the four corners closed, and one refutation

Wave 3 (`scratchpad/probe/mt076/NOTES.md`, harness `EnumProbe.java`) went back
with fixtures built to *discriminate* rather than to demonstrate, and closed
every enumeration corner the two bullets in "Unpinned" carried. It also found
one thing wave 2 could not have seen.

**P-076-0 — `A4Solution.fork(p)` memoizes, so a naive grid probe is
meaningless.** `fork` populates `nextCache` for `p ∈ {-3, -1}` only, but once
populated **returns it for every `p`** (`scratchpad/src794/A4Solution.java
:1843-1855`, verbatim in the probe notes). Calling `sol.next()` and then
`sol.fork(0)` on the same object answers the `next()` question twice — one
`solving p cnf` line for eight `fork` calls, eight byte-identical results. The
GUI never trips it (each button press replaces the displayed solution, so every
press starts from a fresh object). A jar API-shape artifact, not a semantic;
mettle does not replicate it. Every cell below re-solves per `p`.

**P-076-5 — plain `next()` never changes the configuration.** This is the
wave's headline, and it **refines §(i)'s counting rule** (see the correction
there). On `StaticMultiConfig.als` — `sig X` at scope 3 with `some X`, three
genuinely non-isomorphic configs, proven to exist because chained `fork(-1)`
walks all three — plain `next()` yields **exactly 8 solutions and then UNSAT,
every one with `X={X$0}`**. Re-run at `symmetry = 0`, where the raw space holds
all seven non-empty subsets: still 8, still `X={X$0}`. `FieldConfig.als` moves
the static freedom into a field (`one sig P { f: one X }`) and confirms it
again at `symmetry = 0`: 24 consecutive solutions, `f = {P$0->X$0}` in every
one. **The configuration is held.**

**P-076-3 — `fork(-2)` is byte-for-byte `fork(-3)`**, which is *why*: `nextP`
holds the config and varies the path, and so does plain `next()`. Chaining each
six times on `StaticMultiConfig.als` gives identical SHA-256 digests at every
step and exhausts at the same point. §(g)'s wave-2 sentence "`fork(-3)`/
`fork(-2)` held nothing fixed" was an artifact of both wave-2 fixtures having a
*unique* configuration, which made "the config is unchanged" unfalsifiable
there; the part of that sentence about no state prefix being held stands.

**P-076-1 — the `fork(-1)` failure-mode split is a rule, not solver
discretion.** The discriminator is **whether the static relations have any free
primary variables at all**: with none, the config-blocking clause is empty and
the solver re-derives the same model; with some, a real blocking clause goes in
and an exhausted config space reports UNSAT.

| fixture | free static primaries? | alternate config? | `fork(-1)` |
|---|---|---|---|
| `NoStaticFree.als`, `RangeExact3.als` (`one sig X`) | no | — | **byte-identical original** |
| `StaticFreeOneConfig.als` (`sig X`, `#X = 2`) | yes | none non-isomorphic | **UNSAT** |
| `StaticMultiConfig.als` (`sig X`, `some X`) | yes | yes | **SAT, config changed** |

This reproduces and explains wave 2's split exactly: `TraceDemo.als` (T-21) has
only `one sig Counter` — exact-bounded, no free static primaries — hence the
byte-identical original; `EnumDemo.als` (T-20) has free static primaries with
only symmetric alternates — hence UNSAT. Deterministic and portable; mettle
implements it, no divergence needed.

**P-076-2 — each operator's relation to the length sweep.** On
`RangeMulti.als` (`1..3 steps`, two configs):

| operator | length sweep |
|---|---|
| `next()` / `fork(-2)` | **advances** through the range (T-19 reproduced, and reproduced on mt-064's own `RangeEnum.als`) |
| `fork(p)`, `p ≥ 0` | **never moves**; `p ≥ tracelength` is UNSAT |
| `fork(-1)` | **restarts it** from the bottom — the script `-3,-3,-1,-3,-3,-3,-3` walks k=2, k=2, k=3, then comes back at **k=2** with the new config, then advances to k=3 again |

**The `p ≥ 0` rule, sharpened.** T-20/T-21's "forces state `p` onward to a new
value" is really **"require state `p` *itself* to differ; states `p+1 …` are
free"** — which is what Pardinus's `nextS(state, steps, rels)` called with
`steps = 1` means. The discriminating cell: on `RangeExact3.als`, whose
`fact { no Flag }` pins state 0 to one value, **`fork(0)` is UNSAT**, even
though eight solutions with a different state 1 or 2 exist and a "differs
somewhere at or after `p`" constraint would have found one at once. `fork(1)`
on the same fixture returns the *only* shape with a different state 1, diverging
exactly at 1. This also explains `p ≥ k` cleanly — there is no state `p` to
force different. `fork(p)` holds the configuration too.

**P-076-4 — what the enumerator treats as a duplicate, at two levels.**

- *Within one length*: the raw `(per-state contents, loop state)` assignment.
  `RangeExact2.als` yields exactly **2** solutions whose per-state contents are
  **identical** and which differ only in `loopState` — so the loop position is
  part of the solution's identity, and a blocking clause must cover the lasso
  selector, not just the relation primaries. `RangeExact3.als` yields **9**,
  including two that denote the *same infinite trace*
  (`({},{X},{X})` at `loop=2` and at `loop=1` are both `{},{X}^ω`) — both are
  emitted.
- *Across lengths*: the **infinite trace**. The `1..3` sweep emits 2 at k=2 and
  only **6 of the 9** at k=3; the three missing are exactly those whose infinite
  trace was already emitted at k=2. Range total: **8**.

Because `exactly 3 steps` (no shorter length ever visited) keeps all 9 —
*including* the ones representable at length 2 — the exclusion is **not** a
structural minimality constraint inside the length-k encoding. It is the sweep
declining to re-emit an infinite trace it already emitted at a shorter length.
(The two readings coincide extensionally whenever the shorter length is inside
the command's own range, since LTL truth is a property of the infinite trace.)

**The contract, in one table** — this is what mettle implements:

| operator | GUI button | semantics |
|---|---|---|
| `next()` = `fork(-3)` = `fork(-2)` | "New" / "New Trace" | the next raw `(states, loop)` solution **inside the current configuration** at the current length; when that length is exhausted, advance through `[mintrace,maxtrace]`, skipping any solution whose infinite trace was already emitted at a shorter length; UNSAT when the range runs out |
| `fork(-1)` | "New Config" | block the current static assignment, re-run the sweep from `mintrace`. No free static primaries ⇒ the byte-identical original; free but no alternate ⇒ UNSAT |
| `fork(0)` | "New Init" | hold nothing; force state 0 to differ |
| `fork(current+1)` | "New Fork" | hold states `0..current` byte-identical; force state `current+1` to differ; UNSAT if `current+1 ≥ tracelength` |

## (h) The evaluator's per-state story

Closes [alloy6-evaluator.md §4](alloy6-evaluator.md#4-the-temporal-edge-deferred-to-rung-6-d)/§7's
deferred questions, with both direct in-process `eval()` calls and a
cross-check through the real GUI XML-round-trip path (T-25).

**`setCurrentState`'s call sites: client-side state-stepping only, no
solver call.** `edu/mit/csail/sdg/alloy4/OurConsole.setCurrentState(int)`
is called from exactly two places in `VizGUI`'s bytecode: once whenever a
new instance is loaded into the evaluator panel (`current` reset to
whatever the just-solved/just-displayed state is), and once by
`VizGUI.doNavRight()`/`doNavLeft()` — the `<`/`>` toolbar arrows — which
just increment/decrement `VizGUI`'s own `current` field and call
`updateDisplay()`; no `A4Solution` enumeration method (`next`/`fork`) is
invoked by stepping through a trace, only by the five buttons in §(g).
`doNavLeft()` clamps at 0 (`current > 0 ? current-- : no-op`, never goes
negative). `doNavRight()` computes `normalize(current+1, traceLength,
loopLength)` where `normalize(i,len,loop)` is *the same modulo-through-the-loop
formula* independently visible in `A4Solution.toString(int
state)`'s inline logic (`scratchpad/src794/A4Solution.java:1794-1795`) —
the GUI's forward-stepping arrow and the text-rendering path share the
identical wraparound arithmetic, not just a coincidentally similar one.

**`A4Solution.eval(expr, state)`'s validity bounds for `state`, jar-verified
(T-22/T-23), identically across both the lenient `Sig`/`Field` eval path and
the strict `Formula`/`Expression` path, and identically through the real GUI
XML-round-trip path (T-25):**
- `state` in `[0, traceLength)`: the value at that literal state.
- `state >= traceLength`: **wraps through the loop** —
  `((state - loopState) % (traceLength - loopState)) + loopState`, the same
  `TemporalInstance.normalizedIndex` formula wave 1 §(d) cited from source.
- `state < 0`: **silently clamps to state 0 — never throws.** This
  contradicts a naive reading of `TemporalInstance.normalizedIndex`'s own
  bytecode (its guard `state < prefixLength` is trivially true for any
  negative number, which would pass a negative index straight through to
  `List.get` and should throw `IndexOutOfBoundsException`) — the actual,
  jar-verified behavior is a clean clamp with no exception, in every one of
  T-22/T-23/T-25's cells. The exact clamp site was not chased into Kodkod's
  `Evaluator` class (not extracted this wave); behaviorally it is
  indistinguishable from applying the same `Math.max(0, state)`
  `A4Solution.toString(int state)`'s own source applies before its
  loop-wrap arithmetic (`scratchpad/src794/A4Solution.java:1792`) —
  **pinned as observed behavior, mechanism not claimed.**

**Every one of the 11 temporal operators is legal direct evaluator input,
with no special-casing and no rejection, and each evaluates relative to the
given `state`** (**T-24**, `always`/`eventually`/`historically`/`until`/
`after`/`'` all tried against a fixture whose exact per-state trace was
independently pinned in §(f)'s T-13, so every result is hand-verifiable
against the trace, not just internally consistent). `'`/prime specifically
evaluates the wrapped expression *at `state + 1`* — itself subject to the
identical loop-wrap/clamp rules above (so priming at the last state before
a loop correctly wraps into the loop, and priming is well-defined at every
valid `state` input, never a special "last state" edge case). No divergence
was found between direct in-process `eval()` and the real GUI's
XML-round-trip evaluator path for any of this (T-25) — mettle's REPL
(mt-062) can safely implement the simpler in-process shape (matching
[alloy6-evaluator.md §5](alloy6-evaluator.md#5-design-implications-for-mettles-repl-mt-062)'s
existing recommendation) for the temporal edge too, with no fidelity loss.

### `state` is a time index on the infinite trace, not an index into `states[..]` (mt-068, probe P-068-1)

Wave 2's cells all used a fixture whose loop target is its **last** state, so
no state there is ever revisited with a different history, and one reading of
the wrap rule above was left implicit: does `eval(expr, state)` normalize
`state` into `[0, traceLength)` and then evaluate over *that physical state's
own prefix*, or does it evaluate at **logical time `state`** on the unrolled
lasso? mt-068 probed it on a fixture whose loop target is state **0** — so
state 0 recurs — and the first reading is **refuted**
(`scratchpad/probe/mt068/NOTES.md`; fixture forced to `traceLength=2,
loopState=0`, state0 = `no A`, state1 = `some A`):

| expression | state 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| `some A` | false | true | false | true | false | | | | |
| `once some A` | **false** | true | **true** | true | true | true | true | true | true |
| `historically no A` | true | false | **false** | false | false | | | | |
| `before some A` | false | false | **true** | false | true | false | true | false | true |
| `eventually some A` | | | | | | true | true | true | true |
| `always some A` | | | | | | false | false | false | false |

`once some A` is false at state 0 but true at state 2 — the same physical
state — and `before some A` alternates with the **index's** parity, not the
state's. **Pinned: `eval(expr, state)` evaluates at logical time `state` of the
infinite trace.** Present-tense values look wrapped (T-22's finding is the
consequence: logical time `t` sits at physical state
`normalizedIndex(t)`), future operators are pass-invariant (a physical state's
future is the same on every pass), and past operators see the honest logical
past `[0, t]`, which past the first pass contains the earlier passes — the same
true-lasso-history semantics probe **P-D2** (§(l)) found on the *solving* side,
via the same `TemporalInstance.unrolls` machinery.

The GUI never reaches this: `doNavRight` normalizes into `[0, traceLength)`
before storing `current` (above), so its `<`/`>` arrows only ever evaluate
first-pass indices. The behavior is reachable through the API — and therefore
through a CLI that exposes a state index, which is mettle's surface. mettle
implements it (`als_core::eliminate_fragment_at_state`), capping the pass at the
fragment's past-nesting depth, which is exact: `d`-deep past values agree from
pass `d` on. Reproduced jar-free in `crates/mettle/tests/repl.rs`.

## (i) Counting under temporal

**The counting gauge's jar-side baseline generator
(`crates/als-conform/shim/OracleShim.java`'s `countInstances`) enumerates a
temporal command by repeated plain `A4Solution.next()` — exactly `fork(-3)`,
"standard next" per §(g) — with no special-casing for temporal vs. static
commands at that layer.** Source-cited from the actual generator code, not
inferred.

**Reproduced live (T-26):** `leader.als` cmd1 (`run example {eventually some
elected} for 3 but exactly 3 Node, 6 steps`) and cmd3 (`check liveness for
3`) both reproduce the count-baseline's `{"count":1}` exactly (`enumCap=3`
still only finds 1, proving the true count is 1, not an early-stop
artifact); cmd2 (`check safety ...`) reproduces `"unsat"` exactly; cmd0
(`run{} for 4 but exactly 4 Node, 10 steps`) hits its enumeration cap, same
shape as the baseline's cap-hit `10001` (at a much smaller cap, `3`, chosen
per this task's "pick the smallest counting-feasible fixture" allowance —
cmd0's real count is expensive to compute exhaustively and wasn't
attempted). Full command completed in ~100s wall (well under the 120s hard
timeout), covering all four commands in one JVM launch.

**Because §(g)'s T-19 showed `next()` spans the entire `[mintrace,maxtrace]`
steps range rather than staying at the minimal trace length, a temporal
command's count is the number of distinct full traces across every length
in its steps range, not just the minimal length — this is exactly why a
wide range (`10 steps` = `[1,10]`) blows the count up combinatorially
(cmd0's cap hit) while a tight, heavily-constrained range with a strong
formula can have a real count as small as 1 (cmd1/cmd3).** The counting
gauge's temporal arm needs no special per-length or per-config model beyond
what §(g) already pins: it is the same next()-until-UNSAT loop used for
static commands, and its result already naturally spans the steps range by
construction.

### Correction (mt-076, probe P-076-5): the count is **configuration-relative**

The paragraph above is right about the steps range and wrong about the rest of
the space. §(g)'s mt-076 wave shows plain `next()` **never leaves the
configuration the first solve landed on** — proven at `symmetry = 0`, and with
the static freedom in a sig bound and in a field. So a temporal command's jar
count is:

> the number of distinct infinite lasso traces **within a single static
> configuration** — the one the solver happened to find first — across every
> length in the steps range, counting `(states, loop)` assignments raw at each
> length but never re-emitting a trace already emitted at a shorter one.

The live T-26 evidence is untouched (its counts are `1` or cap-hits, where the
distinction cannot show), but the *rule* needed the qualification, and it has a
consequence the counting gauge must own: **exact count parity with the jar is
not achievable by construction for any temporal command whose configuration
space has more than one member**, because the two engines' first solutions pick
different configurations and therefore count different sets. That is
solver-discretion of the same family ADR-0002 already accepts for *which*
instance is shown, not a semantics gap — the algorithm itself is reproduced
verbatim and is deterministic given the first solution.

It is not hypothetical. **Probe P-076-7** ran the jar's `next()` over
`leader.als`'s `check liveness for 3` and mettle's enumerator over the same
command: the jar's first solution is a full three-node ring
(`Node = {Node$0, Node$1, Node$2}`, a real `succ` cycle) which it walks from k=1
through k=3 to the 10001 cap, holding those statics at every step; mettle's is
**the empty model** (`Node = {}`), an equally valid counterexample whose
configuration contains exactly one infinite trace, because with no nodes every
state is identical and every longer lasso de-duplicates onto the k=1 one.
mettle's 1 and the jar's 10001 are both right about different sets.

mettle's gauge therefore **compares but does not cry wolf**: an agreement is a
`count_match`; a *disagreement* on a command with more than one configuration is
the typed skip `skip_temporal_config`; only a unique-configuration command can
raise a temporal `COUNT_MISMATCH`, and there the alarm means what it says.

## (j) Wave-1 loose ends closed

**The correct `SATFactory` id for the bundled electrod binary is
`electrod.elo`** (**T-27** — found by enumerating `SATFactory
.getAllSolvers()` directly instead of guessing more name strings; wave 1's
five guesses, `electrod`/`ElectrodNuXmv`/`ElectrodNuSMV`/`nuXmv`/`NuXmv`,
were all simply wrong spellings). It reports `unbounded=true,
isPresent=true` on this machine (darwin/arm64); the two nuXmv/NuSMV-backed
electrod variants are `unbounded=true` but `isPresent=false` here (their
backing model checkers aren't bundled/found on this platform). Selecting
`electrod.elo` and re-solving T-08b's `UnboundedSteps1.als` (`for 1..
steps`) no longer throws `ErrorAPI("Bounded engines do not support complete
model checking.")` — it solves structurally, though it reports UNSAT for a
fixture that looks trivially SAT by inspection, accompanied by a jar log
warning ("Temporal formula: will be reduced to possibly unsound static
version.") — a genuine, un-investigated curiosity, explicitly not chased
(unbounded/electrod solving remains out of mettle's North-Star scope; see
"Unpinned" below).

**`minprefix=-1` (the implicit "no `steps` lower bound given" sentinel) and
an explicit `minprefix=1` resolve to byte-identical solved results**
(**T-28**: `for 1..10 steps` vs. bare `for 10 steps` on the same model give
identical `getMinTrace()/getMaxTrace()/getTraceLength()/getLoopState()`) —
`ScopeComputer` genuinely normalizes them to the same thing, confirming
wave 1 §(b)'s default-steps claim holds exactly, not just approximately, at
the explicit/implicit boundary.

---

## (k) Implementation-time cite-checks (mt-065)

Facts pinned by jar **source/bytecode reading** (not live probes) while
implementing the static/variable partition and the discriminator; they
extend §(a)/§(d) at the exact granularity the code needed.

**Relation mutability at bounds construction** (`BoundsComputer.java` — the
`isVariable` flag passed at every `addRel`): leaf prim sig `:178` and `in`
subset sig `:241` follow the sig's own flag; the `<Sig>_remainder` relation
`:194` follows the **parent's own** flag, never its children's — a static
parent with a `var` child keeps a *static* remainder, and the jar instead
pins the parent/children union rigid with its own `always (sum' = sum)`
formula at `:206-207` (mt-066 must emit that formula); a field relation
`:448` follows the **field's** flag, not its owner sig's; `util/ordering`'s
`First`/`Next` `:417-418` are ordinary never-`var` fields, so the mt-035
exact pinning always lands on a static relation. Skolem constants are
static (skolemization is off under any temporal operator,
`Skolemizer.java:494-526`).

**Discriminator scoping** (`CompUtil.isTemporalModel`, extending §(a)): the
`var` half is **whole-world** — the `sigs` argument is the complete
reachable-sig list (`TranslateAlloyToKodkod.java:153`), so a `var` sig in
any opened module makes every command temporal; the operator half is
**per-command** — `cmd.formula = globalFacts.and(commandBody)`
(`CompModule.java:2030`), where `globalFacts =
CompModule.getAllReachableFacts()` (`:1905-1913`) holds **free `fact`
paragraphs only** (a sig's appended fact goes to `Sig.addFact`, `:1884`,
and never enters the list), and `commandBody` (`:1975-2014`) is the assert
body for `check a`, the pred/fun's **body substituted directly** for
`run/check p`, or the inline block. The scan is `Expr.hasTemporal()`: the
op set is exactly AFTER/BEFORE/PRIME/HISTORICALLY/ALWAYS/ONCE/EVENTUALLY +
UNTIL/SINCE/TRIGGERED/RELEASES (`Expr$2`, bytecode), and
`VisitQuery.visit(ExprCall)` iterates the call's **`args` only** — it never
descends into the callee's body (bytecode,
`edu/mit/csail/sdg/ast/VisitQuery.class`).

**Source-cited but never live-probed — mt-069 must probe these** (each has
a mettle-side conformance test asserting the cited behavior). *All six were
probed by mt-069; item 4 was refuted and has since been fixed — see §(m).*

1. Non-descent into a *called* pred's body: `pred q { always some A } pred
   p { q } run p` → **not** temporal.
2. A sig's appended fact is outside the scanned formula: `sig A {} { always
   some A } run {}` → **not** temporal.
3. `;` counts as temporal: not an `ExprBinary$Op` member — the jar desugars
   `a ; b` to `a and after b` *before* resolution, so the scanned tree
   holds an AFTER; mettle treats the surface `;` as temporal-bearing.
4. Macro bodies: the jar expands a top-level `let` macro *before*
   `isTemporalModel` scans, so an operator inside a **used** macro makes
   the command temporal. **Probed (K4a/K4b) → mettle's original
   surface-only walk was refuted, and is now FIXED**: the discriminator
   follows a macro use through its recorded `MacroChoice` into the macro
   body (a called pred/fun body is still not descended — K1). See §(m).
5. A `Named` command target with >1 recorded overload: mettle scans all
   overloads; the jar errors on ambiguity, so unreachable in an accepted
   model.
6. Skolem-relation mutability in a temporal model: consistent with
   `Skolemizer.java:494-526`, but no probe pins it directly.

## (l) The LTL-on-lasso expansion cells (mt-066 probe wave)

Pinned by a dedicated 8-fixture / 45-cell live probe wave while
implementing the temporal lowering (harness, fixtures, predictions, and
verbatim jar output: `scratchpad/probe/mt066/` — same discipline as
mt-063; all cells at `symmetry=20, noOverflow=false, sat4j`, every
prediction recorded before running). The load-bearing facts:

1. **Past operators evaluate against the true lasso history, not the
   physical prefix** — the decisive cell is **P-D2** (an alternation
   gadget forcing `traceLength=2, loopState=0`, with
   `always ((once some A) implies (some B))`): honest-physical-prefix
   predicts SAT, the jar answers **UNSAT** (at logical time 2 the trace
   re-enters state 0 with `once some A` now true). Confirmed independently
   via `historically` (P-H1) and a depth-2 nest (P-H2). **This supersedes
   ADR-0015 §2's original "honest prefix" shorthand** (ADR amended); it is
   what the jar's `UNROLL_MAP`/`LEVEL`/`L_PREFIX`/`TemporalInstance.unrolls`
   machinery exists for. mettle implements it by unrolling the timeline
   `d` extra loop copies, `d` = past-nesting depth.
2. **`before` is strong previous** — false at time 0 regardless of body
   (P-A1/A2: both `before (some A)` and `before (no A)` are UNSAT when
   asserted at the initial state), and loop-aware at the back-edge
   (P-J1–J3: `always (after (before φ)) ≡ always φ`).
3. **`once`/`historically` include the present**; at time 0 they collapse
   to it (P-A3–A5).
4. **Operand order for the binary four is standard** — the right operand
   is the goal/obligation: `until`/`releases` (P-B1–B7),
   `since`/`triggered` (P-A6–A9; at time 0 both collapse to the right
   operand). `releases`/`triggered` are the De Morgan duals of
   `until`/`since`.
5. **Prime/`after` step the loop-aware successor** — at `exactly 1 steps`
   the only state's successor is itself (P-C1/C2); prime chains step
   *through* the back-loop (P-C5 UNSAT at k=2 / P-C6 SAT at k=3).
6. **The per-conjunct `always` seam**
   (`TranslateAlloyToKodkod.makeFacts:255-314`): a top-level `fact` and
   the command body bind **state 0 only** (P-F3); field-decl/domain facts
   (`:268-269`/`:281-282`) and sig appended facts (`:307-308`) are
   `always`-wrapped iff temporal (P-F4–F6); a field `disj` group
   (`:291-292`/`:297-298`) is `always`-wrapped iff the decl is `var` —
   mettle keys this last one on is-temporal instead, which additionally
   wraps a *static* `disj` group on a `var` sig (recorded divergence,
   unprobed, narrow).
7. **`BoundsComputer`'s temporal-only structural constraints**, all
   observable and probed: **union rigidity** — a static parent of a `var`
   child keeps its whole population rigid, `always (sum' = sum)`
   (`:206-207`, P-E0/E1); the **`[electrum]` subsig-migration ban** — an
   atom may never move between `var` sibling subsigs (`:164-173`/
   `:195-199`, P-E2/E3); a `var` sig's `one`/`some`/`lone` multiplicity
   holds **at every state** (`:473/477/479`, P-E4/E5).
8. **§(k) item 6 is now closed by probe**: a temporal command still
   skolemizes its outermost non-temporal existentials and the witness is
   **rigid** — identical in every state (P-F1, `skolem $f1_x` byte-equal
   across states); an existential under any temporal operator never
   skolemizes (P-F2, no skolem line).

Still unpinned after this wave (owed to mt-069/mt-067): the minimal
unroll count (mettle's `d` is argued sufficient, not probed minimal —
cost, not correctness); `BoundsComputer.size`'s exact `var`-sig
size-witness quantifier shape (`:284/:288`, masked by rigidity + the
migration ban in practice); the static-`disj`-group-on-`var`-sig
divergence in cell 6; per-state symmetry breaking (mt-067 owns it;
mt-066's tests run at `symmetry=0`).

## (m) The mt-069 probe wave — closing the debt, two STOP-THE-LINE finds

The conformance arm (ADR-0015 §5): banked `buffer.als`'s jar verdicts, then
live-probed every §(k)/§(l) source-cited-but-unprobed cell plus mt-068's
static-eval cell. Full fixtures/predictions/verbatim output:
`scratchpad/probe/mt069/NOTES.md`. Two cells **refuted mettle's shipped
behavior** — real, corpus-reachable (if currently zero-incidence)
divergences, escalated to the tech lead rather than silently patched (per
this bead's ground rules); the rest confirmed what was already shipped or
closed a "masked in practice" cell as still masked. **Both have since been
fixed** in tech-lead-approved follow-ups — see items 1 and 2 below.

> **STOP-THE-LINE — both since resolved:**
> 1. ~~**§(k) item 4, macro-body visibility.**~~ **FIXED (mt-065
>    follow-up, tech-lead approved).** The jar expands a top-level
>    `let` macro's body *before* `CompUtil.isTemporalModel`'s scan runs, so a
>    macro used (in a fact, or directly in a command body) whose body
>    contains a temporal operator makes the command temporal
>    (`isTemporalModel = true`, confirmed both ways — probes **K4a/K4b**).
>    mettle's `als_types::temporal` walked the **surface**
>    AST, where a used macro is `ExprKind::Name(_)` — a leaf, by the same
>    non-descent rule that correctly excludes a called pred/fun's body
>    (K1). mettle therefore misclassified such a command as **static**,
>    rejecting a legal `steps` scope the jar accepts and solves. Verified
>    against the built binary, not just read from source. The scan now
>    follows a macro *use* into its body through the recorded
>    [`MacroChoice`](../../crates/als-types/src/choice.rs) — the same replay
>    seam `als_core::lower` expands macros with, so name resolution is read,
>    not re-derived — while still refusing to follow a func/pred **call**
>    (K1 unchanged). Nested macro uses descend through the call site's own
>    nested choice table; each macro body is walked at most once per scan,
>    which doubles as the cycle guard (Alloy forbids recursive macros, but
>    the walk does not trust that). Regression tests (jar-free, citing
>    K4a/K4b): `crates/als-core/tests/temporal_conformance.rs`'s
>    `a_temporal_operator_in_a_used_macro_is_visible` (both the fact and the
>    command-body shapes),
>    `a_macro_used_through_another_macro_is_visible` (nesting),
>    `a_macro_with_arguments_is_expanded` and
>    `an_unused_macro_body_is_not_scanned` (the last one an **assumption** —
>    K4a/K4b pinned only the *used* shapes). Zero corpus
>    incidence (grepped both corpora for a temporal-operator-bearing
>    top-level macro; none found), so no banked verdict changes.
> 2. ~~**§(l) leftover, `for exactly N..M steps`.**~~ **FIXED (mt-067
>    follow-up, tech-lead approved).** The jar's parser silently collapses
>    `exactly N..M` to `N..N` at `Command`-construction time — the written
>    upper bound `M` is discarded entirely (confirmed via
>    `Command.toString()`'s own rendering, and via `getMinTrace()`/
>    `getMaxTrace()` on a genuinely temporal solve — probes **L6/L6b**).
>    mettle's `als_types::resolve::members::steps_scope` kept the full
>    written range `[N,M]` regardless of the `exactly` flag, so it
>    **searched a wider steps range than the jar does** for this shape — a
>    genuine wrong-verdict class (a model SAT only at length 4 or 5 but not
>    3 would flip mettle's answer relative to the jar's `[3,3]`-bounded
>    UNSAT), not merely a cosmetic difference. It now collapses to `[N,N]`
>    exactly as the jar does, so the *search range*, not just the
>    rendering, matches. Regression tests (jar-free, citing L6/L6b):
>    `crates/als-core/tests/temporal_solve_conformance.rs`'s
>    `exactly_discards_a_written_steps_range_end` (the resolved range, plus
>    the no-`exactly` control) and
>    `exactly_collapses_the_search_range_not_just_its_rendering` (a P-C6
>    prime chain satisfiable only at length 3, put under
>    `exactly 2..4 steps`: UNSAT-within-bound under the collapsed `[2,2]`,
>    SAT at length 3 under the written `2..4` control). Zero corpus
>    incidence either way (the only `exactly`+range-on-temporal-command
>    usage targets a *sig* scope, e.g. `exactly 4 Node`, always a single
>    `N`, never a range).
>
>    **Still unprobed, deliberately unchanged:** `for exactly N.. steps`
>    (`exactly` on an *open* range). L6/L6b covered only the bounded shape;
>    `exactly` stays ignored there, leaving that syntax exactly where it
>    was (`1..` accepted then refused by the bounded engine, T-08b; any
>    other start rejected, T-08a). Not guessed at — it needs its own cell.
>
> Neither item was touched by the probe bead itself:
> `als_types::temporal` was fixed in the mt-065 follow-up above, and
> `als_types::resolve::members::steps_scope` in the mt-067 one.

The rest of the debt, all **CONFIRMS** (mettle's shipped behavior matches
the jar, or a "masked" cell stayed masked on a genuine attempt):

- **§(k) item 1** (non-descent into a called pred's body, K1) and **item 2**
  (an appended sig fact never enters the scanned formula, K2): both
  confirmed exactly as source-cited, with a second, independent
  confirmation via T-03's static-model `ErrorSyntax` on a `steps`-scoped
  variant of the same (non-temporal) command.
- **§(k) item 3** (`;` counts as temporal, K3): confirmed —
  `isTemporalModel = true`, and a `steps` scope on the same command solves
  cleanly (no `ErrorSyntax`), the positive-side confirmation K1/K2 lacked.
- **§(k) item 6** was already closed at mt-066 (P-F1/P-F2); not reopened.
- **§(l) leftover, a static `disj` field group on a `var` sig (L7):**
  attempted construction (a `var` subset sig with two static, disjoint
  fields, one command violating disjointness and one respecting it) —
  mettle and the jar agree on both verdicts (UNSAT / SAT). No divergence
  observed: wrapping a fully rigid (non-`var`-field) formula in `always`
  versus asserting it once at state 0 cannot change its truth value, since
  the formula's own truth never varies by state. Recorded as attempted and
  closed, not merely asserted narrow.
- **§(l) leftover, `BoundsComputer.size`'s var-sig witness shape (L8):**
  attempted construction (a `one`-mult `var` subset sig forced to visit
  every atom of a tight 2-atom pool across a 3-state trace) — mettle and
  the jar agree (SAT, same trace length). Still masked, as the doc already
  said, but now on the strength of a genuine attempt rather than only the
  architectural argument.
- **mt-068's cell, a temporal operator at a STATIC command's evaluator
  prompt (M068):** the jar does **not** throw — it evaluates using the
  same length-1 self-looping trace representation every static solve
  carries internally (`traceLength=1, loopState=0`, the same machinery
  behind the pre-existing "`isTemporal()==true` on a static solve" quirk).
  mettle's current typed refusal here is a **conservative capability gap,
  not a wrong answer** (it declines rather than mis-answers), so this is
  **not** an escalation — recorded as a pinned fact for a later REPL bead.

**Workstream 3 (temporal counting posture), verified, not a new finding —
and since SUPERSEDED by mt-076:**
`als-conform::solve_gauge::execute::classify_temporal_command` gave every
SAT temporal command the typed skip `skip_temporal_trace` unconditionally,
confirmed live against `leader.als` (whose SB-0 baseline holds a real jar
count, T-26) — `agree_sat 3` / `skip_temporal_trace 3` / `COUNT_MISMATCH
0`. That was the deliberate ADR-0015 consequence-4 posture. **mt-076 retired
the bucket**: temporal commands are now enumerated by
`als_core::temporal_enum::TraceEnumerator` and compared like any other, and
`leader.als`'s two real cached counts land `count_match`. The regression test
survives with its polarity inverted
(`leader_als_counts_match_its_real_jar_baseline`).

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

**Wave 2** (`scratchpad/probe/mt064/NOTES.md`; rerun `scratchpad/probe/mt064/rerun_all.sh` plus T-26/T-27's inline one-offs):

| id | Fixture | What it pins |
|---|---|---|
| T-13 | `TraceDemo.als` (mt064) | Trace `toString(-1)` shape + XML: one `<instance>` per state, `looplength = tracelength - loopState`, rigid sigs re-emitted per state |
| T-14 | `Neither.als` (mt063, static contrast) | Static command's XML is the same degenerate 1-`<instance>` shape; `mintrace=-1`/`maxtrace=-1` sentinel written verbatim |
| T-15 | `EnumDemo.als` (mt064) | Base trace shape for the enumeration probes below |
| T-16 | `EnumDemo.als` | Plain `next()` gives 6 pairwise-distinct successive traces |
| T-17/T-17b | `MinLen.als` (mt063) | Only 1 solution before UNSAT at both `symmetry=20` and `symmetry=0` — anomaly, see "Unpinned" |
| T-18 | `RangeEnum.als` (mt064) | Minimal SAT length 2 for a genuine `1..3 steps` range |
| T-19 | `RangeEnum.als` | **Decisive**: `next()` exhausts length-2 solutions then advances to length-3 — enumeration spans the whole steps range |
| T-20 | `EnumDemo.als` | `fork(p)`'s operational classification: `p>=0` holds states `0..p-1` fixed; `fork(-1)`→UNSAT (no alt config) |
| T-21 | `TraceDemo.als` (unique-trace contrast) | Same classification confirmed; `fork(-1)` here returns the identical solution instead of UNSAT (fixture-dependent, see "Unpinned") |
| T-22 | `TraceDemo.als` | `eval(Sig,state)` bounds: wraps through the loop for `state>=traceLength`, clamps to 0 for `state<0`, never throws |
| T-23 | `TraceDemo.als` | Same bounds reconfirmed via the strict `Formula`/`Expression` eval path (`some B`, `A+B`) |
| T-24 | `TraceDemo.als` | All 11 temporal operators legal as direct eval input, results relative to the given state, hand-verified against T-13's trace |
| T-25 | `TraceDemo.als` (`EvalProbe`, GUI XML round-trip) | T-22-T-24 reconfirmed through the real console path — no divergence |
| T-26 | `leader.als` (corpus, via `OracleShim`) | Reproduces the SB-0 count baseline live (`count:1` for cmd1/cmd3, `unsat` for cmd2, cap-hit for cmd0) |
| T-27 | `ListSolvers.java` + `UnboundedSteps1.als` (mt063) | Correct electrod `SATFactory` id is `electrod.elo`; solves structurally but reports an unexplained UNSAT with a "possibly unsound" warning |
| T-28 | ad hoc (`r1`/`r2`) | `minprefix=-1` (implicit) and explicit `minprefix=1` resolve identically |
| **P-068-1** (mt-068) | `scratchpad/probe/mt068/fixtures/LoopPast.als` (loop target = state 0, so state 0 recurs) | **Prediction refuted**: `eval(expr,state)` evaluates at **logical time `state`**, not at the normalized state's first-pass prefix — `once some A` false@0 but true@2; `before some A` alternates with the index's parity (§(h)) |

**mt-069** (`scratchpad/probe/mt069/NOTES.md`; full fixtures/predictions/verbatim there):

| id | Fixture | What it pins |
|---|---|---|
| K1 | `K1_NoDescentIntoCallee.als` | §(k)-1 CONFIRMS: non-descent into a called pred's body, `isTemporalModel=false`, + static-model `ErrorSyntax` on `steps` |
| K2 | `K2_AppendedSigFactOutsideScan.als` | §(k)-2 CONFIRMS: an appended sig fact never enters the scanned formula |
| K3 | `K3_SemicolonIsTemporal.als` | §(k)-3 CONFIRMS: `;` counts as temporal (desugars to `after` pre-resolution) |
| K4a/K4b | `K4a_MacroInFact.als`, `K4b_MacroInCommandBody.als` | §(k)-4 **REFUTES mettle**: the jar expands macro bodies before the discriminator scan (`isTemporalModel=true` both shapes); mettle's surface-AST scan does not — **STOP-THE-LINE** |
| L6/L6b | `L6_ExactlyRange.als`, `L6b_ExactlyRangeTemporal.als` | §(l) leftover **REFUTES mettle**: `exactly N..M steps` silently collapses to `N..N` at parse time (`Command.toString()`/`getMinTrace`/`getMaxTrace` all confirm); mettle keeps the full `[N,M]` range — **STOP-THE-LINE** |
| L7 | `L7_StaticDisjOnVarSig.als` | §(l) leftover CONFIRMS (no divergence found): a static `disj` field group on a `var` sig — always-wrap vs. state-0-only cannot differ for a rigid formula |
| L8 | `L8_VarSigBoundExceedsScope.als` | §(l) leftover CONFIRMS (still masked): `BoundsComputer.size`'s var-sig witness shape — attempted construction, no divergence found |

**mt-076** (`scratchpad/probe/mt076/NOTES.md`, harness `EnumProbe.java`; full
fixtures/predictions/verbatim there):

| id | Fixture | What it pins |
|---|---|---|
| P-076-0 | any (`forkgrid`) | `A4Solution.fork` memoizes into `nextCache` for `p ∈ {-3,-1}` and then returns it for **every** `p` — one solve, eight identical answers. A jar API artifact, not a semantic; every other cell re-solves per `p` |
| P-076-1 | `NoStaticFree.als`, `StaticFreeOneConfig.als`, `StaticMultiConfig.als` | **Closes the T-20/T-21 split**: `fork(-1)` returns the byte-identical original iff the statics have **no free primary variables**; otherwise it blocks the config and reports UNSAT when none is left. Deterministic, not solver discretion |
| P-076-2 | `RangeMulti.als` (`1..3 steps`, two configs) | `next()`/`fork(-2)` advance through the steps range (T-19 reproduced); `fork(p≥0)` never moves the length and is UNSAT for `p ≥ tracelength`; `fork(-1)` **restarts** the sweep at the minimal length for the new config |
| P-076-3 | `StaticMultiConfig.als` (`forkseq -2` vs `-3`) | `fork(-2)` is **byte-for-byte** `fork(-3)`: both hold the configuration and vary the path. Refines §(g)'s wave-2 "held nothing fixed" (unfalsifiable there — those fixtures had a unique config) |
| P-076-4 | `RangeExact2.als`, `RangeExact3.als` vs. `RangeEnum.als`'s `1..3` sweep | The duplicate unit is `(states, loop)` **raw within a length** (2 solutions differing only in `loopState`; 9 at k=3 including two denoting the same infinite trace) and the **infinite trace across lengths** (6 of those 9 survive the sweep; range total 8). `exactly 3 steps` keeps all 9, so the exclusion is the sweep's memory, not a structural minimality constraint |
| P-076-5 | `StaticMultiConfig.als`, `FieldConfig.als` (both also at `symmetry=0`) | **Plain `next()` never changes the configuration** — 8 solutions all at `X={X$0}` with three configs available; 24 solutions all at `f={P$0->X$0}`. Explains the `MinLen.als` anomaly and **corrects §(i)'s counting rule** |
| P-076-7 | `leader.als[3]` (corpus, jar `nextall` vs. mettle's own enumerator) | The configuration divergence on a **real** model, both sides: the jar's first solution is a three-node ring walked to the 10001 cap; mettle's is the empty model with exactly one trace. Found by chasing three SB-20 `COUNT_MISMATCH` rows to the bottom rather than explaining them away |
| P-076-6 | `RangeExact3.als` (`fork(0)` UNSAT), `RangeMulti.als` | Sharpens T-20/T-21: `fork(p)` requires state `p` **itself** to differ (states `p+1…` free) — a fixture whose state 0 is pinned by a fact makes `fork(0)` UNSAT even though eight other solutions exist |
| M068 | `M068_StaticEvalTemporal.als` | mt-068's cell: the jar answers a temporal-operator eval at a STATIC command's prompt (length-1 self-loop, no throw); mettle's typed refusal is conservative, not wrong — not an escalation |

---

## Unpinned / next waves

Honest gaps, not silently glossed over. Wave 2 closed instance/XML
rendering, the enumeration-operator classification, the REPL per-state
story, and counting under temporal scopes (all four of wave 1's headline
deferrals) — what's left is materially smaller and mostly Pardinus-internal
curiosities plus two carried-forward items:

- ~~**Two Pardinus-internal enumeration curiosities**~~ — **both closed by
  mt-076's probe wave** (§(g)'s "The mt-076 probe wave"), and the `MinLen.als`
  anomaly closed with them:
  - The **`MinLen.als` anomaly (T-17/T-17b)** — one raw solution before UNSAT
    even at `symmetry=0`, despite a default scope that looks like it admits
    several non-isomorphic cardinalities — **is P-076-5**: those alternative
    cardinalities are alternative *configurations*, and plain `next()` never
    leaves the configuration it started in. `MinLen.als` was never anomalous;
    wave 2 simply had not yet found the config-hold. Reaching them needs
    `fork(-1)`.
  - The **`fork(-1)` failure-mode split** is **P-076-1**: the discriminator is
    whether the static relations have any free primary variables at all (none ⇒
    the byte-identical original, because the blocking clause is empty; some ⇒
    UNSAT once the config space is exhausted). Deterministic and portable, not
    solver discretion.
  - `TemporalBoundsExpander.extend(...)`'s exact role in incremental
    enumeration (identified structurally in wave 1 §(d)) is **still not
    exercised**, and remains the place to start for anyone wanting the
    *mechanism* behind P-076-4's across-length de-duplication; the *behavior*
    is now pinned without it.
- **`electrod.elo`'s solving semantics, beyond "it's the right id and it
  runs" (T-27).** It reports UNSAT (with a jar-logged "Temporal formula:
  will be reduced to possibly unsound static version." warning) for a
  fixture that looks trivially SAT by inspection. Not investigated —
  explicitly out of scope until unbounded/electrod solving itself becomes
  in-scope for mettle (still Rung-6-out-of-scope per the North Star: the
  bounded default path is the priority). The *id* (`electrod.elo`) is
  pinned; its correctness is not.
- **The `check ... for 1 steps` `NullPointerException` jar bug's root
  cause inside Pardinus** — unchanged from wave 1. The exact repro is
  pinned (T-10a/T-11), the internal mechanism is not. A Ledger decision
  (reproduce the failure vs. diverge, with the divergence recorded in
  `LIMITATIONS.md`) is still owed before Rung 6 implements `check` verdict
  handling at trace-length-1 bounds.
- **Integers/Strings-stay-rigid** is now live-reconfirmed per-state (T-13:
  `Int`/`String`/`seq/Int`/`univ` byte-identical across all three states of
  a forced multi-state trace) — the specific claim in §(d)'s "Static-vs-
  variable relation partitioning" is no longer probe-absent. **The SB-per-state
  / skolem-skip findings in §(d)** remain source-cited only, not
  independently probe-confirmed by inspecting generated SAT clauses —
  unchanged from wave 1, still flagged.
- **The exact bytecode of `TemporalTranslator.expand`/`translate`** —
  unchanged from wave 1, still not disassembled body-for-body. The external
  behavior it produces is independently pinned by two waves of probes now;
  a future wave wanting the literal encoding shape would still need to go
  back to that bytecode.
- **The `sourceFiles`-populated XML round trip for a genuinely multi-state
  instance** (the `<source filename=... content=...>` protocol
  [alloy6-evaluator.md §0](alloy6-evaluator.md#0-the-evaluators-actual-code-path)
  pinned for the non-temporal case) was not independently re-run this wave
  — T-13/T-14 both passed `sourceFiles=null` to keep harness output minimal.
  No reason to expect it interacts differently with multiple `<instance>`
  blocks (the reparse logic already only reads the *first* one's
  `filename` attribute, present and identical in every block per T-13), but
  this specific combination is untested.
- **The exact site inside Kodkod's `Evaluator` class where a negative
  `state` argument gets clamped to 0** (§(h), T-22) was not chased into
  bytecode — `Evaluator` itself was not extracted this wave. The *behavior*
  is solidly pinned (three independent code paths, T-22/T-23/T-25, all
  agree); the mechanism inside Kodkod is not claimed.
- ~~**This document does not yet appear in `docs/README.md`'s reference
  index**~~ — closed: it is indexed there now. (Historical note: the probe
  passes' constraints excluded editing any `docs/` file other than this one;
  the tech lead linked it at merge, next to `alloy6-evaluator.md`/`alloy6-translation.md`.)
