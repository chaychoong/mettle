# Alloy 6 instance XML — the `A4Solution.writeXML` schema (mt-070)

**Status: PINNED (mt-070, tech-lead reviewed 2026-07-27 — the six nominated load-bearing cells X-01/X-03/X-04/X-06b/X-07/X-09 re-run fresh, all byte-identical to the captures). Implemented by mt-071; the Unpinned tail is mt-071's probe debt.**

This document pins the **complete instance-XML schema** the reference
Alloy 6.2.0 jar's `A4Solution.writeXML` (via `A4SolutionWriter.
writeInstance`) emits — the file format underneath every solved instance
Sterling/the GUI displays, every REPL evaluation round-trips through (per
[alloy6-evaluator.md §0](alloy6-evaluator.md#0-the-evaluators-actual-code-path)),
and every temporal trace renders as (per
[alloy6-temporal.md §(f)](alloy6-temporal.md#f-trace-instance-rendering--xml)).
Those two documents already pinned the *protocol* (how the GUI reparses
this file) and the *temporal* shape (one `<instance>` per state, `looplength
= tracelength - loopState`) at the depth each needed for their own bead.
This document goes one level deeper: it is the **exhaustive attribute/
element inventory** — every branch `A4SolutionWriter` can take, read from
its bytecode and then probed live — that a from-scratch Rust
reimplementation of this writer (or a reader aiming for round-trip
fidelity with Sterling) needs.

Per this repo's method: **behavior is pinned by the oracle jar, probed and
recorded with evidence; a claim without a probe run or a source citation is
not pinned.** Every fact below is tagged with a probe id (`X-NN`,
jar-verified 2026-07-27) and/or a source/bytecode citation.

Provenance — same pinned oracle build as every other reference doc in this
directory: `oracle/org.alloytools.alloy.dist.jar` (6.2.0, build commit
`794226dd07b536fe35c5ca44b529417183cd629b`, ADR-0002). Probed under **JDK
21** (Zulu, via the nix dev shell), platform darwin/arm64. Full harness,
exact commands, and verbatim jar output for every `X-NN` id:
`scratchpad/probe/mt070/NOTES.md` (gitignored; rerun with the commands
listed there — there is no single `rerun_all.sh` this wave because
different probes deliberately vary the `macros`/`sourceFiles` arguments
being probed).

`A4SolutionWriter` is **not** present as source in the jar or in
`scratchpad/src794/` (which covers only the translate/solution layer, not
the writer) — pinned here from `javap -p -c -constants` bytecode
disassembly of the class extracted into
`scratchpad/probe/mt061/jarextract/edu/mit/csail/sdg/translator/
A4SolutionWriter.class`. Per `PORTING_RULES.md`: reading jar bytecode to
pin behavior is established practice; no source or decompiled text appears
verbatim anywhere in this repo — `scratchpad/probe/mt070/XmlProbe.java` is
original code calling the same public API the bytecode traces show,
structured after `scratchpad/probe/mt064/TraceProbe.java`'s and
`scratchpad/probe/mt061/Probe.java`'s established precedent.

---

## Summary — the 8 most load-bearing facts

1. **`<instance>` block count is not always `tracelength`.** When the real
   caller's `macros` list (always `module.getAllReachableUserDefinedFunc()`
   in practice, §6) contains a reachable zero-arg `fun` with a nonzero
   `pastDepth()`, the writer emits `tracelength + extra*(tracelength -
   loopState)` `<instance>` blocks, not `tracelength` — extra unrolled
   passes of the loop, appended, while every block still self-reports the
   *same* `tracelength=`/`looplength=` attribute values (§7, `X-06b`,
   decisive). **A reader must count physical `<instance>` blocks, never
   trust the `tracelength=` attribute as the block count.**
2. **Sig/field/skolem ID numbering is lazy-memoized on first reference,
   not declaration order and not print order.** `map(Expr)` assigns
   `Integer.toString(map.size())` the first time *any* code path touches
   that `Expr` — which can happen while building a *different* sig's
   `parentID=` attribute, well before the referenced sig's own `<sig>` tag
   is written. `univ` typically gets a low-but-nonzero ID this way (§2,
   `X-01`, decisively reconstructed and reconfirmed byte-for-byte).
3. Fields are **interleaved** immediately after their owning sig's
   `</sig>` (via a recursive call before that sig's `writeSig` returns to
   its own caller) — not batched separately (§2, `X-01`).
4. Every field/skolem gets a `<types>` element unconditionally (the
   declared column shape, one `<type ID=.../>` per column); `<tuple>`
   elements are printed **additionally**, before `<types>`, only when the
   relation is actually nonempty in this state (§5, `X-04`).
5. `String` is the **one** builtin sig that gets ordinary `<atom>`
   children — `univ`/`Int`/`seq/Int` structurally never do (explicit
   special-cases in the writer). A string-literal atom's label is its own
   quoted spelling (`"a<b&c'd"`, quotes included), XML-escaped (§6, `X-07`).
6. Subset sigs (`sig X in A + B {}`) are written **outside** the `univ`
   recursion tree, in their own top-level `<sig>` (no `parentID`), with
   one `<type ID=.../>` child per parent — this is how multi-parent `in`
   is encoded (§4, `X-02`).
7. `enum` desugars to an `abstract enum="yes"` sig, one `one`-sig per
   value, **plus a surprise**: an auto-injected `private` singleton
   `ordering/Ord` sig with `First`/`Next` fields providing the enum's
   total order — real, reachable, load-bearing structure in the instance
   XML, not an artifact (§4, `X-02b`).
8. Skolem naming depends on whether the command is named: an anonymous
   `run {}` yields bare `$varname`; a named command (`run foo`/`check
   bar`) yields `$cmdlabel_varname` (§8, `X-05`/`X-05b`) — and zero-arg
   **`fun`s** (not `pred`s) additionally get synthesized `<skolem
   ID="m<i>">` entries from a *separate* ID namespace, because
   `SimpleReporter.writeXML`'s real caller always passes every reachable
   user `fun`/`pred` as the `macros` argument — this is live in every real
   solve, not an opt-in feature (§7, `X-06`).

---

## 1. Root element and `<instance>` attribute inventory

**`<alloy builddate="...">`** is the sole root element, one attribute
(`Version.buildDate()`, a fixed jar-build-time string — constant across
every probe run in this session, not wall-clock; source: bytecode constant
`"<alloy builddate=\""`, `writeInstance`). Children: one or more
`<instance>` elements (§2), followed by zero or more `<source>` elements
(§9), then `</alloy>`. **X-01** through **X-09** (every probe in this
document ran against this root shape).

**`<instance>`'s complete attribute inventory, in this exact print order**
(bytecode-enumerated from the private constructor that is the actual
per-state driver — every `ldc` string constant in that method accounted
for, so this list is exhaustive, not sampled):

| attribute | source | notes |
|---|---|---|
| `bitwidth` | `A4Solution.getBitwidth()` | |
| `maxseq` | `A4Solution.getMaxSeq()` | |
| `mintrace` | `A4Solution.getMinTrace()` | `-1` sentinel for a static command (unchanged from `alloy6-temporal.md` T-14, reconfirmed `X-01`) |
| `maxtrace` | `A4Solution.getMaxTrace()` | same `-1` sentinel |
| `command` | `A4Solution.getOriginalCommand()` | XML-escaped via `Util.encodeXML` (singular); `"Run "`/`"Check "` prefix + a `Command.toString()`-shaped body — `"Run run$1 for 3"` (`X-01`), `"Check allSame for 3"` (`X-05b`), `"Run run$1 for 3 but 3..3 steps"` (`X-03`, confirming the `exactly N steps`→`N..N` collapse pinned in `alloy6-temporal.md` L6/L6b independently reconfirmed at the instance-XML layer) |
| `filename` | `A4Solution.getOriginalFilename()` | XML-escaped; a plain public field the *caller* must set (`opts.originalFilename`) — unset gives `filename=""` and breaks the evaluator's reparse, per `alloy6-evaluator.md §0` |
| `tracelength` | `A4Solution.getTraceLength()` | **not** reliably the `<instance>` block count — see §7 |
| `looplength` | computed inline, `tracelength - getLoopState()` | matches `alloy6-temporal.md` §(f) exactly |
| `metamodel="yes"` | present iff `sol == null` | **only** in the separate `writeMetamodel` static entry point (§10) — never co-occurs with a real solved instance |

No `overflow`/`noOverflow` marker exists anywhere in this attribute set —
confirmed by exhaustive `ldc` string-constant enumeration in the writer's
bytecode, not just absence-from-samples (source-cited, not independently
re-probed with a `noOverflow`-toggled fixture; see "Unpinned"). **X-01**
through **X-03** jar-verify every attribute except `metamodel` (§10,
source-only).

## 2. Sig/field ID numbering — the lazy-memoization scheme

**IDs are assigned by `map(Expr)`: a private `IdentityHashMap<Expr,
String>`, `id = Integer.toString(map.size())` the first time any code path
looks up that `Expr` — memoized, never reassigned.** `writeSig` is
recursive: for a `PrimSig`, it fully recurses into every child
(`children(sig)`: `Sig.NONE`→`[]`; `Sig.UNIV`→the `toplevels` list of
sigs whose direct parent is `UNIV`, built from the `sigs` argument at
construction time; otherwise→the sig's native subsig list) **before**
printing its own `<sig>` tag. Printing a sig's own tag calls `map(self)`
first (its own ID), then, if it has a parent and isn't `UNIV`,
`map(sig.parent)` for `parentID=` — so **a parent frequently gets its ID
assigned while a child's tag is being built, well before the parent's own
tag is printed.**

**Jar-verified decisively, `X-01`** (`sig A {}; sig B extends A {}; sig C
{ f: B }`): print order top-to-bottom is `seq/Int, Int, String, B, A, C,
f, univ`; ID order is `seq/Int=0, Int=1, univ=2, String=3, B=4, A=5, C=6,
f=7`. `univ` (last in print order) got ID `2` (third-lowest) because
`Int`'s own tag-building looked up `map(Int.parent==UNIV)` for its
`parentID=` attribute, before `Int`'s own tag finished and long before
`univ`'s own tag was ever built — the exact mechanism above, reconstructed
byte-for-byte against the observed output (full trace in
`scratchpad/probe/mt070/NOTES.md` §2).

**Consequence for a Rust reimplementation:** a writer that assigns IDs in
sig-declaration order, or in DFS pre-order, will **not** byte-match the
reference jar's numbering. Reproducing this exact scheme is only worth
doing if byte-for-byte XML parity with the reference jar is a stated goal
(e.g. for Sterling interop testing) — see "Design implications" below.

**Fields are interleaved, not batched**: `writeSig` calls `writeField` for
every field of the current sig immediately after printing that sig's own
`</sig>`, before returning to its caller — confirmed by `X-01`'s output
(`<field label="f">` appears between `this/C`'s `</sig>` and `univ`'s
`<sig>`, mid-recursion, not at the end of the file).

**A sig's returned (pre-subtraction) atom tupleset accumulates across
children so a parent only prints atoms not already claimed by a
descendant** — each atom appears exactly once in the file, under its most
specific (leaf) sig, even through multi-level `extends` chains.
`A4TupleSet.minus(null)` (a leaf sig with no children) behaves as
identity, not an exception (behaviorally confirmed, `X-01`; no null guard
visible in the disassembly, not chased further).

## 3. `<sig>` attribute inventory, exhaustively

All boolean-ish attributes below print as bare presence (`attr="yes"`,
never `attr="no"`) — each is gated on a Java field being non-null;
absence means false. Exhaustive per the bytecode's `ldc` string-constant
list for `writeSig`:

| attribute | meaning | probe |
|---|---|---|
| `label` | fully-qualified sig name (`this/A`, `seq/Int`, `univ`, ...) | all |
| `ID` | this sig's `map()`-assigned ID | all |
| `parentID` | present iff `PrimSig && sig != UNIV`; the sig's declared parent's ID | `X-01` |
| `builtin="yes"` | `Sig.builtin` — the four builtins only | `X-01` |
| `abstract="yes"` | | `X-02` |
| `one="yes"` | | `X-02` |
| `lone="yes"` | | `X-02` |
| `some="yes"` | (not directly exercised this wave — bytecode-symmetric with `one`/`lone`, low risk; see "Unpinned") | source only |
| `private="yes"` | | `X-02` |
| `meta="yes"` | present for internal `resolveMeta`-synthesized sigs (§0.6 of NOTES.md); checked and found **not reachable** from an ordinary command | `X-03` (absence confirmed) |
| `exact="yes"` | `SubsetSig.exact` only; the connective-keyword syntax that sets it wasn't identified this wave (`sig X in A+B` gives `exact=false`) | source only, unpinned trigger |
| `enum="yes"` | co-occurs with `abstract="yes"` on the enum's parent sig | `X-02b` |
| `var="yes"` | `var sig` | `alloy6-temporal.md` T-13, reconfirmed `X-03` |

**The four builtins, exact labels**: `univ` (no `parentID`, the recursion
root), `Int` (`parentID` = univ), `seq/Int` (`parentID` = Int — a genuine
structural subsig of `Int`, not a separate hierarchy), `String`
(`parentID` = univ). All four `builtin="yes"`. `univ`/`Int`/`seq/Int`
**never** get `<atom>` children (explicit sig-identity special-case in the
bytecode, gated `sig==UNIV || sig==SIGINT || sig==SEQIDX`); **`String`
does** — see §6. `X-01`/`X-03`/`X-07`.

**Subset sigs (`sig X in A + B {}`)** are written **outside** the `univ`
recursion, in a separate driver loop over the `sigs` argument filtered to
`instanceof SubsetSig`, **after** the whole `univ` tree. No `parentID`
(the `parentID`-printing branch is gated on `instanceof PrimSig`, which
`SubsetSig` is not); instead, one `<type ID="..."/>` child per parent —
this is the multi-parent encoding. `X-02` (`SomeSub in A + B` → `<sig
label="this/SomeSub" ID="10"><atom .../><type ID="4"/><type ID="6"/>
</sig>`, printed last, no `parentID`).

**`enum { Red, Green, Blue }` desugars to**: an `abstract` sig `Color`
(`enum="yes" abstract="yes"`), and one `one sig` per value, each
`extends Color` (`one="yes" parentID=<Color's ID>`). **Surprise, not
guessable from the surface grammar alone**: the writer also emits a
`private="yes"` singleton `ordering/Ord` sig plus `private="yes"`
`First`/`Next` fields providing the enum's implicit total order — real,
reachable structure in the instance, not a probe artifact. `X-02b`.

## 4. `<atom>` naming

Ordinary sig atoms: `<SigLastComponent>$<N>` (`A$0`, `B$1`, `Sing$0`),
`N` counting within that sig's own bound, not globally (`X-01` etc.,
consistent with prior pinned docs — no new claim). Enum-value/namespaced
sigs use their full simple label the same way (`ordering/Ord$0`, `X-02b`).

**String-literal atoms**: label = the literal's **own quoted spelling**,
quote characters included, not just the bare content — `"a<b&c'd"`
(quotes literally part of the label), then XML-escaped per §8. `X-07`.
This is the one case where an atom label is user-influenced text rather
than a synthesized `Sig$N` — the escaping rules in §8 matter specifically
here (and in `<source content=...>`, §9).

**Temporal atom pool numbering**: across a multi-state trace, an atom
that disappears and a later-appearing atom of the same sig are **not**
guaranteed to reuse the same number — `X-03`'s `this/A` shows `A$0` at
state 0, empty at state 1, `A$1` (not `A$0` again) at state 2. Consistent
with a scope-fixed atom universe whose occupancy varies per state, not
per-state fresh numbering (no new claim beyond what `alloy6-temporal.md`
already implies; independently reconfirmed here).

## 5. `<field>` elements

Attributes, in print order: `label`, `ID`, `parentID` (the owning sig's
ID — **every** field has this, unconditionally, since a field always
belongs to exactly one sig), `private="yes"`, `meta="yes"`, `var="yes"`.
`X-01` (plain), `X-03` (`var` field — not separately exercised this wave
beyond the already-pinned `alloy6-temporal.md` T-13 finding for var
*sigs*; var *fields* were not independently re-probed here, see
"Unpinned"), `X-02b` (`private`).

**Tuple/type body, jar-verified precisely (`X-01`, `X-04`):**
- **Every field gets a `<types>` element, unconditionally** — one `<type
  ID="..."/>` per column of the field's *declared* type, where column 0
  is always the owning sig (a field's tuple arity is always its declared
  Alloy arity **+ 1**, for the owning sig). `X-04`: `g: A -> B -> A` on
  sig `C` → 4-column tuples (`C, A, B, A`), `<types>` has 4 `<type>`
  entries.
- **`<tuple>` elements are printed additionally, before `<types>`, only
  when the relation is nonempty in this state.** An empty field (`X-04`'s
  `empty: A -> B`, forced empty by a fact) prints `<types>` alone, no
  `<tuple>`s. This resolves an ambiguity a first bytecode pass left open
  (see `scratchpad/probe/mt070/NOTES.md` §0.7) — settled empirically, not
  worth chasing byte-for-byte in the disassembly once the probe answered
  it.
- Each `<tuple>` contains exactly `arity` `<atom label="...">` children,
  no separators beyond XML structure.

Arity ≥ 3 fields (`X-04`) follow the identical shape, just with more
`<atom>`s per `<tuple>` and more `<type>`s in `<types>`.

## 6. `<skolem>` elements — two independent kinds

**Ordinary skolems** (existential witnesses from `some x: ... | ...`,
whether from a `run` or a `check` counterexample): `sol.getAllSkolems()`,
written via `writeSkolem`. Attributes: `label`, `ID` (from the **same**
shared `map()` IdentityHashMap sigs/fields use — a skolem's ID can
collide numerically... no, cannot collide since it's the same map, just
sharing the ID *namespace*, not colliding), then the same
`<tuple>`/`<types>` body as a field (§5), gated the same way (empty
skolem → `<types>` only — not independently probed empty, but the
mechanism is the same `writeExpr` call).

**Naming, jar-verified both ways:**
- **Anonymous command** (`run { some x: A, y: A | x != y } for 3`): bare
  `$varname` — `$x`, `$y`. `X-05`.
- **Named command** (`assert allSame {...}; check allSame for 3`, an
  existential inside a negated assertion body):
  `$<cmdlabel>_<varname>` — `$allSame_x`, `$allSame_y`. `X-05b`. This
  matches the convention already pinned in `alloy6-translation.md` §10
  (T9) and `alloy6-evaluator.md` §1 (E-24), which only demonstrated the
  named case; `X-05` closes the anonymous-command gap those left open.

**Macro-derived skolems — a second, independent mechanism.** Every
reachable, zero-arg (`Func.count()==0`) `fun`/`pred` whose zero-arg call's
type `hasTuple()` (i.e. it's a relational `fun`, not a Boolean `pred`)
gets a synthesized `<skolem>` too, **one per `<instance>` block**, from
the `macros` argument to `writeXML`. Label: the func's fully-qualified
label with any leading `$` characters stripped, then prefixed with
exactly one `$` (`"this/Best"` → `"$this/Best"`). **ID: a separate
`"m" + i` namespace** (`i` a 0-based counter incrementing only on
successful emission), **not** looked up via the shared `map()`
IdentityHashMap sigs/fields/ordinary-skolems share. `X-06`
(`fun Best: one A { A }` → `<skolem label="$this/Best" ID="m0">`; a
zero-arg `pred trivial` in the same fixture correctly produces **no**
entry — negative space confirmed, not just unobserved).

**This mechanism is live in every real solve, not an API-only edge
case**: `SimpleReporter.writeXML` (bytecode-traced,
`edu/mit/csail/sdg/alloy4whole/SimpleReporter.class`) — the GUI/CLI's own
caller — always passes `module.getAllReachableUserDefinedFunc()` as
`macros`, i.e. every reachable user-defined `fun`/`pred`, unconditionally.
`scratchpad/probe/mt064/TraceProbe.java`'s own XML probes (T-13/T-14,
`alloy6-temporal.md` §(f)) never exercised this because that harness
always passed `Collections.emptyList()` — this document's harness
(`scratchpad/probe/mt070/XmlProbe.java`) deliberately supports both and
defaults its interesting probes to `macros=all` to match the real path.

## 7. The extra-`<instance>` mechanism (macros × `pastDepth`)

**The single most load-bearing, easy-to-miss finding in this document.**
`writeInstance`'s driver computes, over every macro eligible for §6's
synthesized-skolem treatment: `extra = max(extra, Func.getBody().
pastDepth())`. It then constructs one `A4SolutionWriter` (one
`<instance>` block) for every `state` in `[0, getTraceLength() +
extra*(getTraceLength() - getLoopState()))` — **strictly more blocks than
`tracelength` whenever `extra > 0`.** Every block still self-reports the
*same* `tracelength=`/`looplength=` attribute values (§1); only the
physical block *count* changes.

**`X-06b`, decisive, jar-verified exactly**: a `var sig A` temporal
fixture solved to `traceLength=3, loopState=1` (so `tracelength - loopState
= 2`), with a reachable zero-arg `fun PastWitness: set A { {x: A | once x
in A} }` (a comprehension whose inner formula uses `once`, giving the
comprehension expression `pastDepth()==1` — see the note below on how
this spelling was found) → predicted block count `3 + 1*2 = 5` →
**actual: exactly 5 `<instance>` blocks**, matching to the block.

**Design note on the fixture**: the first attempt spelled the past
operator directly on an expression (`fun PastWitness: set A { before A
}`) and was **refuted** — `before` fails `ErrorType` typecheck both as a
`fun` body and as a bare evaluator expression (confirmed via
`scratchpad/probe/mt064`'s `evalstates` mode:
`eval("before A", state=0) THREW ErrorType: This expression failed to be
typechecked`). So `before`/`historically`/`once` are **formula-only**
surface syntax — they do not apply directly to a relational expression,
despite `alloy6-temporal.md` §(a)'s note that all 11 temporal operators
share one Java enum (`ExprUnary$Op`); that note is about the
*implementation*, not a claim that every operator type-checks on every
expression shape. The working spelling nests the past operator inside a
set-comprehension's inner formula (`{x: A | once x in A}`), which
type-checks as a `set A`-typed expression whose `pastDepth()` is
apparently computed through the nested formula. Full detail:
`scratchpad/probe/mt070/NOTES.md` §8.

**Consequence for a Rust reimplementation**: a writer targeting Sterling/
GUI round-trip fidelity must replicate this unrolling exactly (both the
`extra` computation and the resulting block range) if it wants byte
parity with the reference jar on any model with a reachable past-nested
zero-arg `fun`; a reader must never assume `<instance>` block count equals
`tracelength` — it must count blocks directly, and reconcile against
`tracelength`/`looplength` only for the *per-block* loop-wrap math (per
`alloy6-temporal.md` §(f)/§(h)), not for "how many states does this file
describe."

## 8. Escaping rules

Two escaping call sites confirmed, both using the writer's standard
5-entity XML escaping (`&amp; &lt; &gt; &quot; &apos;`), plus newlines
rendered as numeric character references (`&#x000a;`) inside `content=`:

- **`<source filename=... content=...>`'s `content` value** — the
  entire embedded module source text, verbatim, escaped. `X-03`'s
  `TemporalSrc.als` source (containing `<`, `&`, `'`, `"` in its own
  comments) round-trips through `&lt;`, `&gt;`, `&amp;`, `&apos;`,
  `&quot;`, and `&#x000a;` for every newline, exactly as expected of a
  faithful escaper.
- **`<atom label="...">` for a String-literal atom** — `X-07`:
  `"a<b&c'd"` → `&quot;a&lt;b&amp;c&apos;d&quot;`.

Sig/command/skolem labels made of ordinary Alloy identifiers never contain
XML metacharacters (the grammar doesn't allow it), so those attributes
were not separately escaping-tested — the two sites above are the only
places user-influenced text with arbitrary characters reaches the XML.

## 9. `<source>` elements — full protocol, including the flagged temporal gap

Written **once per `sourceFiles` map entry**, **after every `<instance>`
block**, immediately before `</alloy>` — never interleaved with, or
duplicated across, `<instance>` blocks. Two attributes: `filename`
(escaped via the array form, `Util.encodeXMLs`), `content` (escaped, §8).
Order = the `sourceFiles` map's iteration order; this harness (like
`scratchpad/probe/mt061/Probe.java` before it) supplies the same
`LinkedHashMap` `CompUtil.parseEverything_fromFile`'s own `loaded`
out-param populates while parsing, so the order pinned here is "module
parse order" (the real GUI path's own map-construction site,
`SimpleReporter`'s static `ConstMap<String,String> latestKodkodSRC`
field, was not independently bytecode-traced to its construction — see
"Unpinned").

**Closes `alloy6-temporal.md` §(f)'s flagged gap**: `sourceFiles`
populated **together with** a genuine multi-`<instance>` temporal file.
`X-03` (a `var sig` fixture, `open`ing a second real module,
`tracelength=3`): three `<instance>` blocks, all with byte-identical
`filename=` (confirmed by inspection), followed by exactly three
`<source>` elements at the end — **no interaction effect, no
duplication, no divergence from the non-temporal case.**

**Surprise, `X-03`**: `sourceFiles` had **three** entries, not the two
the fixture's own `open` graph would suggest — the jar's bundled
`util/integer` standard-library module was silently included at a
synthetic path `/$alloy4$/models/util/integer.als`, even though the
fixture never wrote `open util/integer`. Not chased to a root cause (a
parser-internals question); flagged so a reader/writer doesn't assume
`sourceFiles`'s keys are exactly the user's own `open` graph.

## 10. `writeMetamodel` — a separate, out-of-scope entry point

`A4SolutionWriter.writeMetamodel(sigs, filename, out)` is a distinct
static method (not reachable via `A4Solution.writeXML`) that constructs
the same `A4SolutionWriter` with `sol=null`. This changes three things:
`metamodel="yes"` gets added to `<instance>` (§1); `writeSig`/`writeField`
skip any sig/field with `isMeta != null` entirely (the opposite of the
normal-instance case, where meta sigs are written *with* `meta="yes"` if
reachable — see §3); the whole call uses fixed metadata
(`bitwidth=4,maxseq=4,mintrace=1,maxtrace=1,tracelength=1,loopState=0,
command="show metamodel"`). Source-cited only (`javap` disassembly of
`writeMetamodel`), not independently probed — this document's remit is
the *instance* XML a solved `run`/`check` produces, and this path never
co-occurs with one.

## 11. Round-trip authority

`A4SolutionReader.read(sigs, xml)` accepted the writer's own output on
both a static (`X-08a`) and a genuine multi-`<instance>` temporal
(`X-08b`) file, reproducing identical `satisfiable()`/`getTraceLength()`/
`getLoopState()`. This is the acceptance bar any mettle instance-XML
writer must clear at minimum. Not exhaustive: round-trip was not
independently re-run against the subset-sig/enum/arity-3/skolem/macro-
extra-instance shapes in §§3-7 (see "Unpinned").

## 12. Determinism

Writing the same solved `A4Solution` twice in one process (`X-09a`) and
running the identical fixture+command in two completely separate JVM
invocations (`X-09b`) both produced byte-identical output, including the
`builddate=` attribute (a fixed jar-build-time string, confirmed constant
across every probe run in this session — not wall-clock). This is the
determinism claim that actually matters for a conformance-style
comparison (not just "stable within one process").

---

## Design implications for a mettle instance-XML writer/reader

- **A reader must never assume `<instance>` block count == `tracelength`**
  (§7). If mettle ever needs to *parse* Sterling-produced or reference-jar-
  produced instance XML (e.g. a future differential-testing harness that
  diffs against real jar output), it must count blocks and treat
  `tracelength`/`looplength` as per-block loop-wrap metadata only.
- **The lazy-memoization ID scheme (§2) is a genuine choice point, not
  free.** Byte-parity with the reference writer requires replicating the
  exact print-order-driven `map()` semantics; a simpler, more idiomatic
  scheme (e.g. assign IDs in a stable pre-order sig traversal at write
  time) is very likely fine for mettle's own purposes and is *not*
  required for scorecard conformance (ADR-0002's scorecard compares
  solve *verdicts*, not instance-XML bytes) — but if a Sterling-interop
  goal is ever adopted, this is exactly the kind of divergence that would
  need a deliberate SEMANTICS_LEDGER.md entry, one way or the other.
- **The macros mechanism (§§6-7) is not optional to model** if mettle
  ever writes instance XML for Sterling/GUI consumption: the real jar's
  own CLI/GUI path always passes every reachable `fun`/`pred` as
  `macros`, so any zero-arg relational `fun` in a model (common — e.g.
  named intermediate expressions) will produce a `<skolem ID="m<i>">` in
  the reference output, and any such `fun` with nested past operators
  will change the *block count*. A writer that ignores `macros` entirely
  (as `alloy6-temporal.md`'s own T-13/T-14 probes did) produces XML that
  is valid but observably different from what the reference jar's actual
  GUI/CLI path would write for the same model.
- **The `enum` auto-injected `ordering/Ord` sig (§3) and the always-
  present `util/integer` source entry (§9) are both examples of "the
  instance is bigger than the user's own model."** Any mettle code that
  reasons about "the sigs/fields/modules in this instance" from a
  purely-surface-syntax view of the user's `.als` file will undercount —
  both of these are real, reachable, jar-verified parts of a solved
  instance's structure.

---

## Unpinned

Honest gaps, not silently glossed over — full detail and reasoning for
each in `scratchpad/probe/mt070/NOTES.md`'s "Unpinned / not chased this
wave" section:

- **`SubsetSig.exact="yes"`'s triggering surface syntax** — source-cited
  (`exact = !par.label.equals("in")`, `CompModule.java:1500-1511`) but the
  actual second-keyword spelling that reaches this branch (other than the
  internal `resolveMeta`-synthesized `this/static$`/`this/var$`, which are
  source-constructed, not parsed from user syntax) was not identified
  within this wave's budget. The parser grammar file itself was not found
  in `scratchpad/src794`'s decompile set (likely only present as
  generated parser code inside the jar, not yet extracted).
- **`this/static$`/`this/var$` meta-sig reachability** was checked on only
  one `var`-using fixture and found absent; not checked across a wider
  variety of temporal models, and the actual explicit `$`-syntax that
  *would* make them reachable (the dedicated "show metamodel"-adjacent
  feature, if any exists outside `writeMetamodel` itself) was not
  identified.
- **`writeMetamodel`/`metamodel="yes"`** (§10) — source-cited only, not
  independently probed; deliberately out of scope for this document's
  "instance XML from a solved run/check" remit.
- **`overflow`/`noOverflow` writing no marker to instance XML** — confirmed
  by exhaustive bytecode string-constant enumeration, not independently
  reprobed with a `noOverflow`-toggled live fixture.
- **`ConstMap`'s ordering guarantee** for the real GUI's own
  `latestKodkodSRC` field (as opposed to this harness's `LinkedHashMap`
  substitute) was not bytecode-traced to its construction site.
- **Why `util/integer` is always pulled into `sourceFiles`** even absent
  an explicit `open` (§9) — parser-internals question, not chased.
- **Round-trip (`A4SolutionReader.read`) acceptance** was only exercised
  on the two simplest shapes (§11) — not on subset sigs, enum, arity-3+
  fields, ordinary/macro skolems, or the extra-instance (§7) shape.
- **`some="yes"`** (the fourth multiplicity attribute, alongside
  `one`/`lone` which were both jar-verified) was read from the bytecode's
  symmetric `ldc` string constant but not independently exercised with a
  live `some sig` fixture this wave — low risk given `one`/`lone` both
  confirmed the pattern exactly as read.
- **`var` **fields** specifically** (as opposed to `var` sigs, which are
  thoroughly pinned) were not independently probed with a field that is
  itself `var`-declared and whose value changes across states — only the
  attribute's presence was confirmed structurally from the bytecode
  listing (§5). Low risk (identical code shape to `var` sig's
  already-pinned attribute-printing branch) but not empirically closed.
- **`command=`'s exact grammar for every scope-decoration combination**
  (`but N int` together with `steps`, multiple `but` clauses, etc.) — only
  the three shapes this wave's fixtures happened to produce were observed
  (§1's table). Very likely just `"Run "`/`"Check "` + `Command.
  toString()` (consistent with everything seen, and with
  `alloy6-temporal.md`'s independent `Command.toString()` pins), but not
  exhaustively cross-checked against every scope-clause combination that
  document already pins for `Command.toString()` in isolation.
