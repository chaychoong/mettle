# Alloy 6 evaluator — pinned contract for mettle's REPL (mt-061)

This document pins **exactly how the reference Alloy 6.2.0 GUI's expression
evaluator behaves** — the "Evaluator" console reachable from Sterling/the
visualizer after a `run`/`check` command solves — so mettle's REPL
(mt-062, since shipped) could be implemented *from this contract*, not from memory or from a
plausible-looking API read. Per this repo's method: **behavior is pinned by
the oracle jar, probed and recorded with evidence; a claim without a probe
run or a source citation is not pinned.**

This is a **different** pinned contract from
[alloy6-translation.md](alloy6-translation.md), which pins the
solve/translate pipeline (Rung 3). This document picks up *after* a command
has solved: given a satisfiable `A4Solution`, what can a user type into the
evaluator, and what do they see back.

Provenance — same pinned oracle build as every other reference doc in this
directory: `oracle/org.alloytools.alloy.dist.jar` (6.2.0, build commit
`794226dd07b536fe35c5ca44b529417183cd629b`, ADR-0002). Probed on this
machine under **OpenJDK 26** (Temurin) — no JDK 21 was available here despite
the task brief assuming it; the jar's manifest requires only
`osgi.ee=JavaSE;version=17` and no behavioral difference is expected or was
observed. All facts below are tagged with a probe id (`E-NN`, jar-verified
2026-07-25) and/or a source citation. Full harness, exact commands, and raw
verbatim jar output for every `E-NN` id: `scratchpad/probe/mt061/NOTES.md`
(gitignored; re-run with `scratchpad/probe/mt061/probes.sh`).

The `edu.mit.csail.sdg.alloy4*`/`alloy4whole.*`/`alloy4viz.*` GUI classes are
**not** bundled as source in the jar or in `scratchpad/src794/` (which covers
only the translate/solution layer). §0's mechanism was read from `javap -c
-p` bytecode disassembly of the extracted classes (per PORTING_RULES: reading
jar bytecode/source to pin behavior is established practice; no source or
decompiled text appears verbatim anywhere in this repo or under `crates/` —
`scratchpad/probe/mt061/Probe.java` is original code calling the same public
API in the same order the bytecode showed).

---

## 0. The evaluator's actual code path

The console a user types into is `edu.mit.csail.sdg.alloy4.OurConsole` (a
`JScrollPane`). Its `do_command(Computer, String)` method (bytecode offsets
0-230+ of `javap -c OurConsole.class`) does, on Enter:

1. Trim the input; if empty, do nothing (return silently — **no** call into
   the evaluator at all for blank input).
2. Call `Computer.compute(new Object[]{ trimmedInput,
   String.valueOf(this.current) })` — a **two-element `Object[]`**: the raw
   input text, and the string form of `current`, a mutable `int` field on
   `OurConsole` set via `setCurrentState(int)` — the trace-state index (§4).
3. On success, render `result.toString().trim()` in the console's "good"
   (dark) style. On any `Throwable`, render `throwable.toString()` in the
   "bad" (red) style. **The rendering is always driven by `.toString()`** —
   there is no separate structural renderer; whatever Java type `compute`
   returns, only its string form ever reaches the user.

The `Computer` behind this specific console (as opposed to the separate
`enumerator` `Computer` used for "Next instance" navigation — not traced
further, out of scope here) is traced through
`edu.mit.csail.sdg.alloy4viz.VizGUI` (`private final Computer evaluator`,
passed into `new OurConsole(evaluator, ...)`) to
`edu.mit.csail.sdg.alloy4whole.SimpleGUI`'s static `evaluator` field, which
is assigned exactly once to a `new SimpleGUI$6()`.

`SimpleGUI$6 implements Computer` is the evaluator itself. Its `compute`
method (full bytecode disassembly in
`scratchpad/probe/mt061/jarextract/edu/mit/csail/sdg/alloy4whole/SimpleGUI$6.class`,
traced via `javap -p -c -constants`) does, in order:

1. **Two-shot protocol.** If the argument is a `java.io.File`, store its
   absolute path in an instance field `filename` and return `""` — this is
   how the GUI points the evaluator at *which solved instance's XML* to
   evaluate against (called once per newly-shown instance, from
   `VizGUI`/`SimpleReporter`, **not** from the console itself). If the
   argument is not a `String[]`, or the first element trims to empty, return
   `""`.
2. **Reload the instance from its written XML, not the live solve object.**
   `new XMLNode(new File(this.filename))` — the XML that
   `A4Solution.writeXML` produced right after solving (§ below). If the root
   isn't `<alloy>`, throw.
3. Find the `<instance filename="...">` child — the *original* `.als` file
   path — and every `<source filename="..." content="...">` child (the
   embedded, frozen source text of every module involved in the solve).
4. **Re-parse the entire original module from that embedded source**, not
   from disk: `CompUtil.parseEverything_fromFile(A4Reporter.NOP,
   loadedFilesMap, origFilename, 1)` — `loadedFilesMap` is checked before any
   real file I/O, so this works even if the `.als` file on disk has since
   changed or been deleted. (The trailing `1` is the "implicit `this`" mode
   flag — `2` only when `Version.experimental &&
   A4Preferences.ImplicitThis.get()`, not the default.)
5. **Reconstruct a fresh `A4Solution` purely from the XML**:
   `A4SolutionReader.read(world.getAllReachableSigs(), xml)`. This is a
   *different object* from the one the solver produced — its atom/tuple data
   comes entirely from what got written to XML.
6. **Register every atom and skolem name as a module-level global**:
   `for (ExprVar atom : ans.getAllAtoms()) world.addGlobal(atom.label,
   atom);` and the same for `ans.getAllSkolems()`. This is *why* a literal
   instance atom name (`A$0`) or a skolem name (`$foo_x`) parses and
   resolves at all — they are not special syntax, they are ordinary
   identifiers bound as globals in the reparsed module (§1).
7. Any exception up to this point (steps 2-6) is swallowed and rethrown as
   `new ErrorFatal("Failed to read or parse the XML file.")`.
8. **Parse the user's expression**:
   `CompUtil.parseOneExpression_fromString(world, input)`. Source
   (`scratchpad/src794/CompModule.java:982-996`): this wraps the raw input
   as `"run {\n" + input + "}\n"` and parses it through the **ordinary
   pred/fun-body grammar** — this is why formulas, comprehensions, `let`,
   plain relational expressions, and arithmetic all share one input slot:
   they are all valid pred-body productions. If the parse yields zero
   top-level funcs, `ErrorSyntax("The input does not correspond to an Alloy
   expression.")` (source-only; not exercised by any probe — see §7).
9. **Evaluate**: `ans.eval(expr, Integer.parseInt(a[1])).toString()` — `a[1]`
   is the state-index string from step 2 of `do_command`.
10. `kodkod.engine.fol2sat.HigherOrderDeclException` (thrown when the typed
    expression needs higher-order quantification the evaluator can't
    handle) is caught and rethrown as `new
    ErrorType("Higher-order quantification is not allowed in the
    evaluator.")`. Every other exception from steps 8-9 propagates
    uncaught out of `compute`, back to `OurConsole.do_command`'s catch-all
    (step 3 above) — rendered as `throwable.toString()`.

**`A4Solution.eval(Expr, int state)`** itself
(`scratchpad/src794/A4Solution.java:1050-1075`) is a thin dispatcher:

- `expr instanceof Sig` or `instanceof Field` → a *separate*, more lenient
  path (`eval(Sig,state)`/`eval(Field,state)`,
  `scratchpad/src794/A4Solution.java:982-1036`) that **never throws** for
  `!solved` or unsatisfiable — it silently returns an empty `A4TupleSet`.
  (Reachable in the evaluator's own re-solved object only in principle;
  see §(b)'s UNSAT finding for why this path is moot in practice.)
- Otherwise: `if (!solved) throw ErrorAPI("This solution is not yet solved,
  so eval() is not allowed.")`; `if (eval == null) throw ErrorAPI("This
  solution is unsatisfiable, so eval() is not allowed.")`; resolve
  ambiguity/errors on the expr; translate via
  `TranslateAlloyToKodkod.alloy2kodkod`; dispatch on the Kodkod result type:
  - `IntExpression` → `eval.evaluate(...) + (eval.wasOverflow() ? " (OF)" :
    "")` — **note this concatenation makes the return value a `String` in
    every case**, not a `java.lang.Integer` as the method's own javadoc
    claims (`scratchpad/src794/A4Solution.java:1039-1041` says "returns ...
    a java Integer, or a java Boolean" — that's stale; confirmed by E-12,
    E-28-E-30, E-32 all showing `javaType=java.lang.String`).
  - `Formula` → `eval.evaluate((Formula) result, state)` — a
    `java.lang.Boolean`.
  - `Expression` → `new A4TupleSet(eval.evaluate((Expression) result,
    state), this)`.

**Where the XML's `<instance filename="...">` comes from** (needed to make
a headless probe harness replicate this at all — `A4Solution` itself has no
filename field): `A4SolutionWriter.writeInstance` bytecode traces this
attribute to `A4Solution.getOriginalFilename()` →
`originalOptions.originalFilename`
(`scratchpad/src794/A4Solution.java:593-594`,
`scratchpad/src794/A4Options.java:112`) — a plain public field on
`A4Options` that the **caller** (SimpleGUI/CLI) must set before
`execute_command`; never auto-derived by the translator. Left unset, the
written XML has `filename=""` and step 4 above fails to find the source
("File cannot be found") — this is a genuine trap `scratchpad/probe/mt061/Probe.java`
fell into and had to fix (see its header comment and
`scratchpad/probe/mt061/NOTES.md`).

**Also traced** (`SimpleReporter.resultSAT`/`resultUNSAT` bytecode):
`writeXML` — and the static `latestKodkod*` fields the evaluator's `File`
hand-off depends on — is called **only** from `resultSAT`.
`resultUNSAT`'s bytecode contains no reference to `writeXML` or any
`latestKodkod*` field. This is the basis for §(b)'s UNSAT finding.

---

## 1. Input surface (a)

All of the following are accepted through the **single** grammar slot
described in §0 step 8 (`run { <input> }`, parsed as a pred body) — there is
no separate "formula mode" vs. "expression mode."

- **A literal instance atom name** (`A$0`): resolves because §0 step 6
  registers it as a module global bound to the `ExprVar` for that atom.
  Reflexivity-controlled: `A$0 = A$0` → `true` (E-02). Renders as a
  singleton set `{A$0}` (E-01).
- **A MODULE-QUALIFIED atom name** (`so/Ord$0`) — an atom of a sig declared in
  an *opened* module — is accepted too, and by the same mechanism: §0 step 6
  registers the label **verbatim**, alias and slash included, and the global
  table is keyed by the whole string, so the name resolves by **exact match**
  and never through module-qualified lookup (mt-098, probes E-50–E-58; fixture `scratchpad/probe/mt098/m2_surface.als`, banked as `crates/mettle/tests/fixtures/repl/qualified.als`).
  Consequences, all jar-verified:
  - **Every atom label the instance prints is legal input.** Two aliases of one
    module give two distinct atoms (`so/Ord$0 = tw/Ord$0` → `false`), and
    `enum` implicitly opens `util/ordering` with *no* alias, so a third,
    bare-module-qualified atom (`ordering/Ord$0`) can exist alongside them.
  - **Nothing else that looks like one is.** `so/Ord$1` (real alias, no such
    index), `zz/Ord$0` (no such alias), `A$9` (index beyond scope) and
    `so/Nope$0` are each `ErrorSyntax`, `The name "…" cannot be found.`
  - **The sig's own qualified name is NOT reachable**: `so/Ord` is likewise
    "cannot be found", because only atoms and skolems are ever `addGlobal`'d.
    That asymmetry is the proof the mechanism is an exact global-table hit
    rather than ordinary name resolution.

  mettle implements this as `Cx::env_get_qualified`, consulted by
  `resolve_name`/`infer_name`/`spine_head` and gated on fragment (evaluator)
  input, so a module-qualified name in a *model* still means what it says.
- **A skolem name** (`$foo_x`, from `run foo { some x: A | ... }`):
  likewise a registered global (`ans.getAllSkolems()`). E-24: `$foo_x` →
  `{A$0}`. Naming convention (`$<cmdlabel>_<varname>`) matches the existing
  pin in [alloy6-translation.md §10, probe T9](alloy6-translation.md#10-probe-log-jar-verified-2026-07-16).
- **`univ`, `iden`, `Int`, `String`, `none`** — all parse and evaluate as
  ordinary built-in relations (E-03 through E-07). See §3 for exact
  rendering, including a load-bearing ordering divergence from other pinned
  docs.
- **Quantified formulas** (`all x: A | x = x`) — parse and evaluate to a
  `Boolean`, rendered `true`/`false` (E-09).
- **Comprehensions** (`{x: A | some x}`) — parse and evaluate to a tupleset
  (E-10).
- **`let`** (`let x = A | x`) — parses and evaluates fine (E-11).
- **`#` cardinality** (`#A`) — evaluates via the `IntExpression` path,
  renders as a bare numeral **string** (`"1"`, E-12) — see §3's
  int-vs-Int-set distinction, which this is the canonical example of.
- **Int arithmetic, `plus[3,4]` and `3.plus[4]`** — both syntaxes accepted
  identically (E-13/E-14, both render `{7}`). **Important, non-obvious
  pin**: `plus[...]` type-checks to the built-in `Int` **set** type, not
  primitive `int`, so it goes through the `Expression` branch of
  `A4Solution.eval`, not the `IntExpression` branch — it renders as a
  singleton tupleset `{7}`, **not** a bare `7`. **Careful — "int-typed renders
  bare" is not the rule** (mt-099): `int[3]` is int-typed and renders `{3}`
  (E-65), as does a bare literal `3` (E-59). Only `#e`, a `sum x: d | e`
  quantifier, and a shift render bare; §3 states the measured rule in full.
  Note `sum` is two different things here — the *quantifier* renders bare, the
  `sum e` *cast* does not. Verified this is not a
  probe artifact: `3 + A` (E-19) renders `{3, A$0}` — confirming `+` is
  Alloy's set-union operator over `Int`/relations, never arithmetic
  addition (`plus[]` is the only spelling for arithmetic `+`).
- **A `sig` declaration or a command typed literally** (`sig Foo {}`,
  `run {}`) — **rejected**, and rejected **identically** to any other
  malformed input (`+++`, a comment-only line): a generic
  `edu.mit.csail.sdg.alloy4.ErrorSyntax`, `"Syntax error at line 1 column
  N:\nThere are 38 possible tokens that can appear here:\n! # ( * @ Int NAME
  NUMBER STRING String ^ after all always before disj eventually fun
  historically iden int let lone no none once one pred seq set some steps
  sum this univ { } ~"` (E-15, E-16, E-17, byte-identical text; E-20 for the
  comment-only variant, same message at a different column). There is
  **no** special-cased "that's a declaration, not an expression" error —
  the parser simply can't start a pred-body production with those tokens.
- **An unknown identifier** (`NoSuchName`) — `ErrorSyntax`, `"Syntax error
  at line 1 column 1:\nThe name \"NoSuchName\" cannot be found."` (E-18).
  Source: `CompModule.hint()`,
  `scratchpad/src794/CompModule.java:970-976`.
- **Calling a pred/fun defined in the model:**
  - *With* the right arguments (`isEmpty[A]`) — evaluates normally,
    `Boolean` result (E-21).
  - *Without* arguments where required (`isEmpty`) — `ErrorType`, a long,
    specific message naming the pred, its parameter list, and why the
    (missing) call doesn't match:
    ```
    Type error at line 1 column 1:
    Name cannot be resolved; possible incorrect function/predicate call; perhaps you used ( ) when you should have used [ ]

    This cannot be a correct call to pred this/isEmpty.
    The parameters are
      s: {this/A}
    so the arguments cannot be empty.
    ```
    (E-22, verbatim). A `fun` behaves the same way for arity mismatches
    (E-43 below is the same message shape for a builtin `fun`).

## 2. Evaluation context (b)

- **Bitwidth/maxseq are inherited from the *solved command*, not any
  global default — proven, not assumed.** Same model, two commands with
  different `but N int`: `Wide` (`for 3 but 4 int`) and `Narrow` (`for 3 but
  3 int`). Evaluating `plus[3,4]` against `Wide`'s solved instance gives
  `{7}` (fits in 4-bit range −8..7, no wrap); against `Narrow`'s instance
  gives `{-1}` (3-bit range −4..3; 3+4=7 wraps mod 8 to two's-complement
  `-1`) (E-25/E-26). Confirmed again with `sum x: A | 7`: `7` at 4-bit
  (E-29), `-1` at 3-bit (E-28).
- **`noOverflow` does not change eval-position arithmetic wraparound.**
  E-26 vs. E-27 (same `Narrow` command, `noOverflow=false` vs. `true`):
  identical `{-1}` result both times. E-32 vs. E-33 (a fresh
  overflow-producing `sum`, `7+7=14 → -2` mod 16 at 4-bit): identical `-2`
  both times. `noOverflow` at solve time only gates whether the *solved
  formula itself* is allowed to overflow (rejects the SAT model if it
  would) — it does not change how the evaluator computes arithmetic on an
  ad hoc expression typed into the console afterward, which always wraps
  silently. See §7 for the still-open question of when (if ever) the
  `A4Solution.eval` source's `" (OF)"` marker actually appears — it did not
  appear in any of these probes despite genuine overflow occurring both in
  a freshly-typed expression (E-31: `plus[7,7]` → `{-2}`, no marker) and
  in a `sum` typed as primitive `int` (E-32/E-33, no marker).
- **Evaluation tracks "the current instance" purely via the two-shot
  `File`/`String[]` protocol — no hidden auto-advance.** `ProbeNext`
  (`scratchpad/probe/mt061/ProbeNext.java`) solves a command with several
  satisfying instances, takes instance #1 and instance #2 via
  `A4Solution.next()` (the same enumeration API "Next instance" in the GUI
  uses), writes+reparses+evaluates `#A` against each, then re-evaluates
  against instance #1's XML again. Result (E-36): `0`, then `1`, then `0`
  again — proving "current instance" is nothing but "whichever XML file the
  evaluator's `Computer.compute(File)` was last pointed at"; revisiting an
  older instance's XML after a newer one was loaded works exactly like
  loading it the first time.
- **Evaluation after UNSAT: the evaluator is never pointed at an UNSAT
  result in the first place — not an API exception the user ever sees.**
  Two facts combine: (1) `A4SolutionWriter.writeInstance` (which
  `A4Solution.writeXML` calls) explicitly checks `sol.satisfiable()` first
  and throws `ErrorAPI("This solution is unsatisfiable.")` immediately if
  not (E-34/E-35, confirmed via the same headless harness attempting the
  full round-trip against an UNSAT command); (2) traced in
  `SimpleReporter`'s bytecode, `resultUNSAT` **never calls `writeXML`** and
  never touches the `latestKodkod*` static fields the evaluator's `File`
  hand-off reads from — only `resultSAT` does. So a UNSAT command simply
  never refreshes what the evaluator points at: if no instance was ever
  successfully shown, there is nothing to evaluate against (the eval
  console has nothing loaded); if an earlier command *did* solve, the
  evaluator silently keeps pointing at that stale instance, unaffected by
  a later UNSAT command. **The low-level `A4Solution.eval()` guard
  messages** (`"This solution is not yet solved, so eval() is not
  allowed."` / `"This solution is unsatisfiable, so eval() is not
  allowed."`, `scratchpad/src794/A4Solution.java:1056-1059`) are real and
  correctly documented from source, but are effectively **unreachable
  through the GUI's own flow** — they matter only to a direct API consumer
  (e.g. mettle's own REPL, if it calls an equivalent `eval` directly
  in-process rather than replicating the XML hand-off) — see "Design
  implications for mettle" below.

## 3. Rendering, exactly (c)

All rendering is `.toString()` on whatever `A4Solution.eval` returns (§0);
there is no separate pretty-printer in this path (no table view — that's
the instance visualizer's different code path, out of scope here).

| Value shape | Expression | Verbatim rendering | Probe |
|---|---|---|---|
| Empty set | `none` | `{}` | E-06 |
| Singleton atom | `A$0` | `{A$0}` | E-01 |
| Unary relation, several atoms | `B` (3 atoms) | `{B$0, B$1, B$2}` | E-37 |
| Binary relation | `f` (B one-to-one A) | `{B$0->A$0, B$1->A$0, B$2->A$0}` | E-38 |
| Ternary relation | `g` (A -> B) | `{C$0->A$0->B$0, C$0->A$0->B$1, ..., C$2->A$0->B$2}` | E-39 |
| Bare integer (an `IntExpression`, see the rule below) | `#A` | `1` (as `String`, not `Integer` — §0) | E-12 |
| Singleton `Int` atom (an int-*typed* expression that is nonetheless an `Expression`) | `3`, `int[3]`, `plus[3,4]` | `{3}`, `{3}`, `{7}` | E-59, E-65, E-13 |
| Boolean | `some A` | `true` | E-08 |
| String atom (exists in instance) | `"hello"` (model uses it) | `{"hello"}` | E-40 |
| `seq` value | `Holder.xs` | `{0->A$0, 1->A$0}` — an ordinary binary (index -> element) relation, **no special seq syntax** | E-42 |
| Parse error | `sig Foo {}` / `run {}` / `+++` | `Syntax error at line 1 column 1:\nThere are 38 possible tokens that can appear here:\n! # ( * @ Int NAME NUMBER STRING String ^ after all always before disj eventually fun historically iden int let lone no none once one pred seq set some steps sum this univ { } ~` | E-15/E-16/E-17 |
| Unknown-name error | `NoSuchName` | `Syntax error at line 1 column 1:\nThe name "NoSuchName" cannot be found.` | E-18 |
| Type error, bad call arity | `isEmpty` (no args) | see §1, verbatim block | E-22 |
| Type error, bad call args | `plus[A,3]` | `Type error at line 1 column 1:\nName cannot be resolved; possible incorrect function/predicate call; perhaps you used ( ) when you should have used [ ]\n\nThis cannot be a correct call to fun integer/plus.\nThe parameters are\n  n1: {Int}\n  n2: {Int}\nso the arguments cannot be\n  this/A (type = {this/A})\n  Int[3] (type = {Int})` | E-43 |
| Type error, bad join | `A[B]` (arity/type mismatch) | `Type error at line 1 column 1:\nThis cannot be a legal relational join where\nleft hand side is this/B (type = {this/B})\nright hand side is this/A (type = {this/A})` | E-44 |
| Unknown string literal | `"hello"` (string not in this instance's bounds) | `Fatal error at line 1 column 1:\nString literal "hello" does not exist in this instance.` (`ErrorFatal`) | E-49 |
| Higher-order quantification | (an expr needing HO quant) | `ErrorType("Higher-order quantification is not allowed in the evaluator.")` | §0 step 10, source-cited only — not independently exercised this pass; low risk, mechanism is unambiguous from bytecode |

**Bare numeral vs. singleton `Int` atom — the full rule (mt-099).** It is
tempting to read §1's `#`/`sum` remark as "int-typed renders bare". That is
**wrong**, and the counterexamples are ordinary input. Every cell in E-59-E-79
was measured to carry Alloy type `{Int}` with `is_int` set — the type is *not*
the discriminator. What decides is the branch of `A4Solution.eval` the root
lands in (§0): an `IntExpression` renders bare, an `Expression` becomes an
`A4TupleSet` and renders `{n}`.

> **The root renders bare iff it is a cardinality `#e`, a `sum x: d | e`
> quantifier, or a shift (`<<` / `>>` / `>>>`). Every other Int-valued root
> renders `{n}`** — a numeral literal (E-59-E-64), `int[e]` / `sum e` /
> `sum[e]` (E-65-E-69), an `integer/*` fun call (E-13), and any Int-valued
> relation or join.
>
> Four constructs are **transparent** — they pass the question through rather
> than answering it: parentheses and a one-expression block `{e}` (E-79); a
> user-written `Int[e]` (E-70-E-72); a `let`, whose body's own translation
> decides (E-73-E-75); and an `if-then-else`, which reads its **then** branch
> alone, by this same rule (E-76/E-77).

Two halves of that are counter-intuitive and worth stating plainly. First,
`int[e]` / `sum e` — the operator that *means* "convert to a primitive int" —
renders as a **set**: it is `CAST2INT`, and §0 step 8's
`parseOneExpression_fromString` ends by re-resolving the parsed body against
its own type (`scratchpad/src794/CompModule.java:988-990`), which re-wraps a
`CAST2INT` root as `Int[int[e]]`; `visit(ExprUnary)` case `CAST2SIGINT` is
`cint(x.sub).toExpression()`
(`scratchpad/src794/TranslateAlloyToKodkod.java:888-889`), an `IntToExprCast`,
which **is** an `Expression`. `CARDINALITY` gets no such wrapper and stays
`cset(x.sub).count()`, an `IntExpression`. Second, and symmetrically, that same
re-resolve *strips* a user-written `CAST2SIGINT` at the root, so `Int[#A]`
renders bare `1` while `int[#A]` renders `{1}`.

Honest limit on that second half: the strip rule was characterized
**behaviorally**, not traced to a bytecode branch (`ExprUnary` is not in
`scratchpad/src794/`). "A top-level `CAST2SIGINT` is stripped unless its sub is
a `CAST2INT`" fits all 20+ cells measured, but it is recorded as a behavioral
pin, not a source citation.

mettle implements this as `Lowerer::fragment_sort`, selected by
`FragmentRoot::Evaluator` on `FragmentInput` — deliberately *not* an edit to
`Lowerer::sort_of`, which asks the different (in-expression coercion) question
and is the solve path's classifier too. The instance-XML writer's macro bodies
keep `sort_of` (`FragmentRoot::Value`), because `A4SolutionWriter` builds its
`Expr` directly and never goes through the evaluator's re-resolve.

**Tuple/atom ordering — a genuinely load-bearing, non-obvious pin.**
`univ`/`Int` rendered through the evaluator's actual (XML-round-trip) path
come out in this order: string atoms (if any) first, then **int atoms in
the order `-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, ..., 7`** (not sorted by
value, not the two's-complement bit-pattern order you'd expect), then sig
atoms in declaration/index order (E-03, E-05, E-45, E-46 — all four models
tested reproduce the identical `-1..-8, 0..7` int sub-order). This
**diverges** from [alloy6-translation.md §1.3/probe
T8](alloy6-translation.md#10-probe-log-jar-verified-2026-07-16)
(`univ={A$0, -8, -7, …, 7}` — sig atoms *first*, ints ascending from `-8`),
which is not a contradiction once reconciled: T8 dumps
`A4Solution.toString()` against the **live, just-solved** object, whereas
the evaluator path (E-03 etc.) rebuilds a *fresh* `A4Solution` from the
written-then-reread XML via `A4SolutionReader.read`, which orders things
differently. A same-model comparison probe evaluating `univ` directly
against the live object (`scratchpad/probe/mt061/LiveEval.java`, not the
pinned GUI path — kept only for this reconciliation) reproduces the
T8-style order exactly: `{A$0, B$0, B$1, B$2, C$0, C$1, C$2, -8, -7, ..., 0,
1, ..., 7}`. **Both orders are correctly pinned; they are pinned facts about
two different code paths.** See "Design implications for mettle" below.

## 4. The temporal edge, deferred to Rung 6 (d)

Out of deep-probing scope per this task's brief; recorded lightly with real
(not guessed) evidence. `A4Solution.eval(Expr expr, int state)` already
always takes a state index — even for the non-temporal, trace-length-1 case
tested throughout §1-3, where `state` is always `0`. For a `var`-using model
(`fixtures/Var.als`: `var sig A {}`, `fact { always (some A => after no A)
}`), evaluating the same expression `A` at `state=0` vs. `state=1` gives
different, fact-consistent answers: `{A$0}` at state 0, `{}` at state 1
(E-47/E-48) — confirming the mechanism generalizes correctly to temporal
models without any special-casing in `A4Solution.eval` itself. What Rung 6
actually needs to pin (not attempted here): how `OurConsole.current` gets
set as the user steps through a trace in the GUI (the `setCurrentState(int)`
call sites — presumably wired to "Next state"/"Previous state" navigation,
not traced), what `mintrace`/`maxtrace`/loop-state bounds mean for valid
`state` values, and whether `Prime`/`always`/`until` operators are even
legal to type into the evaluator directly (untested).

## 5. Design implications for mettle's REPL (mt-062)

- **The single-grammar-slot trick (§0 step 8) is worth replicating
  directly**: implement one "parse as pred body" entry point for REPL
  input, not a bifurcated formula-vs-expression parser. It is what makes
  §1's whole input surface (formulas, comprehensions, arithmetic, bare
  relational expressions) fall out for free from one code path, matching
  the jar's actual behavior including its rejection shape for declarations
  and commands (§1, E-15-E-20 — reject with the parser's generic
  "unexpected token" message, not a bespoke error).
- **Atom/skolem-name-as-global (§0 step 6) is the right shape to port**,
  not the XML round-trip that produces it. mettle's REPL should register
  atom/skolem names as resolvable identifiers directly against its
  in-process solved-instance representation; there is no reason to
  replicate the jar's XML-serialize-then-reparse implementation detail
  (that exists in the jar only because the GUI's evaluator panel is a
  separate Swing component decoupled from the solver's live object, not
  because it's semantically required).
- **The universe-order divergence (§3) is a real choice point, not
  resolved by this document.** If mettle's REPL evaluates directly against
  its live, in-process solved instance (the natural, idiomatic thing to
  do, and the only thing so far pinned as *semantically necessary*), its
  `univ`/`Int`/multi-atom-relation rendering will naturally match the
  **T8/§1.3 solve-time order** (sig atoms, then ascending ints), not the
  GUI-console's XML-round-trip order pinned in §3 above. Byte-for-byte
  matching the GUI console's specific order would require deliberately
  replicating the XML round-trip's reordering effect for its own sake —
  not recommended; the conformance scorecard (ADR-0002) does not diff
  instance tuple order, and REPL output isn't scorecard-gated the same way.
  Flag this choice explicitly when mt-062 is scoped, and record whichever
  order is chosen in SEMANTICS_LEDGER.md with a test.
- **The `int`-vs-`Int`-set distinction (§1, §3) must be implemented
  faithfully** — it is a real Alloy typing rule (`plus[]`/`minus[]`/etc.
  are `Int`-set-typed; `#`/`sum` are primitive-`int`-typed), not a jar
  quirk, and it changes rendering shape (`{7}` vs `7`).
- **UNSAT/not-yet-solved eval guards (§2) should still be implemented** at
  the API level even though the GUI never surfaces them to a user — a
  from-scratch REPL is free to let a user query eval state more directly
  than the jar's GUI does (e.g. immediately after entering a command that
  turns out UNSAT), so mettle's own `ErrorAPI`-equivalent messages are
  worth having, using the jar's exact wording as the baseline
  (`scratchpad/src794/A4Solution.java:1056-1059`) unless there's a reason
  to diverge (record any divergence in LIMITATIONS.md).

## 6. Probe log (jar-verified 2026-07-25)

Harness: `scratchpad/probe/mt061/Probe.java` (single solve + single eval,
replicating §0's mechanism call-for-call: solve → `writeXML` → reparse from
XML → `parseOneExpression_fromString` → `eval`) and
`scratchpad/probe/mt061/ProbeNext.java` (multi-instance variant for E-36).
Oracle: `oracle/org.alloytools.alloy.dist.jar` (6.2.0). Every invocation
wrapped in `timeout 60` (`run.sh`). Full commands and complete verbatim
output for every id below: `scratchpad/probe/mt061/NOTES.md`; rerun
everything with `scratchpad/probe/mt061/probes.sh`.

| id | Fixture / cmd | Input | Verdict / observation |
|---|---|---|---|
| E-01 | Base.als#0 | `A$0` | `{A$0}` |
| E-02 | Base.als#0 | `A$0 = A$0` | `true` (reflexivity control) |
| E-03 | Base.als#0 | `univ` | ints-then-sigs order, see §3 |
| E-04 | Base.als#0 | `iden` | pairs in the same atom order as E-03 |
| E-05 | Base.als#0 | `Int` | all 16 int atoms, `-1..-8,0..7` order |
| E-06 | Base.als#0 | `none` | `{}` |
| E-07 | Base.als#0 | `String` | `{}` (no string atoms in this instance) |
| E-08 | Base.als#0 | `some A` | `true` |
| E-09 | Base.als#0 | `all x: A \| x = x` | `true` |
| E-10 | Base.als#0 | `{x: A \| some x}` | `{A$0}` |
| E-11 | Base.als#0 | `let x = A \| x` | `{A$0}` |
| E-12 | Base.als#0 | `#A` | `"1"` (String, IntExpression path) |
| E-13 | Base.als#0 | `plus[3,4]` | `{7}` (Expression path, not IntExpression — §1) |
| E-14 | Base.als#0 | `3.plus[4]` | `{7}` (same as E-13, dot-syntax equivalent) |
| E-15 | Base.als#0 | `sig Foo {}` | generic `ErrorSyntax`, 38-token list |
| E-16 | Base.als#0 | `run {}` | identical to E-15 |
| E-17 | Base.als#0 | `+++` | identical to E-15 |
| E-18 | Base.als#0 | `NoSuchName` | `ErrorSyntax`, "cannot be found" |
| E-19 | Base.als#0 | `3 + A` | `{3, A$0}` — proves `+` is union, not arithmetic |
| E-20 | Base.als#0 | `-- just a comment` | same generic error, later column |
| E-21 | Funcs.als#0 | `isEmpty[A]` | `false` |
| E-22 | Funcs.als#0 | `isEmpty` | `ErrorType`, verbatim arity-mismatch message |
| E-23 | Funcs.als#0 | `double[3]` | `{6}` |
| E-24 | Skolem.als#0 | `$foo_x` | `{A$0}` |
| E-25 | Bitwidth.als#0 (Wide, 4-bit) | `plus[3,4]` | `{7}` |
| E-26 | Bitwidth.als#1 (Narrow, 3-bit) | `plus[3,4]` | `{-1}` — bitwidth inheritance proof |
| E-27 | Bitwidth.als#1, `noOverflow=true` | `plus[3,4]` | `{-1}` — unchanged |
| E-28 | Bitwidth.als#1 (3-bit) | `sum x: A \| 7` | `"-1"` |
| E-29 | Bitwidth.als#0 (4-bit) | `sum x: A \| 7` | `"7"` |
| E-30 | OverflowSolve.als#0 | `sum x: A \| 0` | `"0"` |
| E-31 | OverflowSolve.als#0 | `plus[7,7]` | `{-2}`, no `(OF)` marker |
| E-32 | SumOverflow.als#0, `noOverflow=false` | `sum x: A \| 7` (|A|=2) | `"-2"`, no marker |
| E-33 | SumOverflow.als#0, `noOverflow=true` | `sum x: A \| 7` | `"-2"`, no marker — unchanged |
| E-34 | Unsat.als#0 | `A` | `writeXML` itself throws `ErrorAPI("This solution is unsatisfiable.")` before eval is reachable |
| E-35 | Unsat.als#0 | `some A` | same as E-34 |
| E-36 | MultiInstance.als#0 (`ProbeNext`) | `#A` against inst.#1, #2, #1-again | `0`, `1`, `0` — no auto-advance |
| E-37 | Base.als#0 | `B` | `{B$0, B$1, B$2}` |
| E-38 | Base.als#0 | `f` | `{B$0->A$0, B$1->A$0, B$2->A$0}` |
| E-39 | Base.als#0 | `g` | 9-tuple ternary relation, see §3 |
| E-40 | Str.als#0 | `"hello"` | `{"hello"}` |
| E-41 | Str.als#0 | `A.label` | `{"hello"}` |
| E-42 | Seq.als#0 | `Holder.xs` | `{0->A$0, 1->A$0}` |
| E-43 | Base.als#0 | `plus[A,3]` | `ErrorType`, verbatim bad-call-args message |
| E-44 | Base.als#0 | `A[B]` | `ErrorType`, verbatim bad-join message |
| E-45 | SumOverflow.als#0 | `univ` | same ints-then-sigs order as E-03 |
| E-46 | Str.als#0 | `univ` | string atom first, then ints, then sigs |
| E-47 | Var.als#0, state=0 | `A` | `{A$0}` |
| E-48 | Var.als#0, state=1 | `A` | `{}` |
| E-49 | Base.als#0 | `"hello"` (no such string atom in this instance) | `ErrorFatal`, "String literal ... does not exist in this instance." |
| E-50 | Qual.als#0 | `so/Ord$0` | `{so/Ord$0}` — a module-qualified atom label IS legal input (mt-098) |
| E-51 | Qual.als#0 | `tw/Ord$0` | `{tw/Ord$0}` — a second alias of the same module |
| E-52 | Qual.als#0 | `ordering/Ord$0` | `{ordering/Ord$0}` — `enum` opens `util/ordering` with no alias |
| E-53 | Qual.als#0 | `so/Ord$0 = tw/Ord$0` | `false` — two aliases' atoms are distinct atoms |
| E-54 | Qual.als#0 | `so/Ord$0 = so/Ord$0` | `true` — reflexivity control |
| E-55 | Qual.als#0 | `so/Ord$1` | `ErrorSyntax`, "The name \"so/Ord$1\" cannot be found." |
| E-56 | Qual.als#0 | `zz/Ord$0`, `so/Nope$0` | `ErrorSyntax`, same shape — no such alias / no such sig |
| E-57 | Qual.als#0 | `A$9` | `ErrorSyntax`, same shape — index beyond scope |
| E-58 | Qual.als#0 | `so/Ord` (the SIG by qualified name) | `ErrorSyntax`, "cannot be found" — only atoms/skolems are `addGlobal`'d |
| E-59 | Qual.als#0 / Num.als#0 | `3` (a bare numeral literal) | `{3}` — the Expression path, **NOT** a bare numeral (found mt-098, surface pinned and mettle fixed at mt-099) |

**mt-099 — the numeral/int-cast surface (jar-verified 2026-08-21).** Fixture
`Num.als` (`sig A {}`, `one sig B { v: one Int }`, `fact { B.v = 3 }`,
`run { some A } for 1 but 4 int`; banked as
`crates/mettle/tests/fixtures/repl/numeral.als`). Same harness as above;
44/44 of these cells were re-measured against that exact fixture with mettle
side by side (`scratchpad/probe/mt099/sweep-fixture.txt`). **Every cell below
has Alloy type `{Int}` with `is_int` set** — measured, the `{n}` ones included —
so the int *type* is not what decides; see §3's rule.

| id | Input | Verdict / observation |
|---|---|---|
| E-60 | `-3` | `{-3}` — a negative numeral literal parses, and takes the same Expression path |
| E-61 | `0` / `7` / `-8` | `{0}` / `{7}` / `{-8}` |
| E-62 | `8` (bitwidth 4) | `{-8}` — an **out-of-range literal wraps two's-complement, silently**: no error, no rejection, no `(OF)` marker |
| E-63 | `15` / `16` / `-9` | `{-1}` / `{0}` / `{7}` — same wrap rule |
| E-64 | `Int[3]` / `Int[Int[3]]` | `{3}` — a literal stays the Expression path however it is wrapped |
| E-65 | `int[3]` | `{3}` — **`CAST2INT` renders as a tupleset**, not bare |
| E-66 | `sum[3]` / `sum 3` | `{3}` — the same AST node, the same result |
| E-67 | `int[B.v]` / `sum B.v` | `{3}` — also for a genuine `Int`-valued relation |
| E-68 | `int[#A]` | `{1}` — also for an argument that would itself render bare |
| E-69 | `int[int[3]]` | `{3}` |
| E-70 | `Int[#A]` | `1` — **bare**: a user-written `Int[·]` at the root is *dropped*, so it is transparent, not relational |
| E-71 | `Int[sum x: A \| 1]` | `1` — same |
| E-72 | `Int[B.v]` / `Int[plus[3,4]]` | `{3}` / `{7}` — transparent to a relational argument too |
| E-73 | `let x = #A \| x` | `1` — `let` is substitution (`visit(ExprLet)`), so the body's own translation decides |
| E-74 | `let x = #A \| let y = x \| y` | `1` — transitively, through nested `let`s |
| E-75 | `let x = 3 \| x` / `let x = plus[1,1] \| x` / `let x = 3 \| #x` | `{3}` / `{2}` / `1` |
| E-76 | `(some A => int[3] else 0)` | `{3}` — the ITE reads its **then** branch through this same rule (mt-095's dispatch, refined) |
| E-77 | `(some A => #A else 0)` / `(some A => 3 else 4)` | `1` / `{3}` |
| E-78 | `3 << 1` / `7 >> 1` / `-1 >>> 1` / `#A << 1` | `6` / `3` / `7` / `2` — a **shift** is a `BinaryIntExpression`, so it renders bare |
| E-79 | `(#A)` / `{ #A }` / `#(A+B)` / `#B.v` / `#none` / `#Int` | bare — parentheses and a one-expression block are transparent |

## 7. Unpinned corners (be honest)

- **The `A4Solution.eval` source's `" (OF)"` overflow suffix
  (`scratchpad/src794/A4Solution.java:1066`, `eval.wasOverflow()`) could
  not be triggered.** Tried genuine overflow in three shapes — E-26/E-27
  (boundary-crossing `plus[]` at 3-bit), E-28 (`sum` overflow at 3-bit),
  E-31/E-32/E-33 (`plus[7,7]`/`sum` overflow at 4-bit, both `noOverflow`
  settings) — all silently wrap with no marker. Either `eval.wasOverflow()`
  (a Kodkod-side `Evaluator` flag, source not available to read directly —
  Kodkod is a separate bundled dependency, not covered by
  `scratchpad/src794/`) tracks a narrower condition than "did this ad hoc
  `evaluate()` call overflow" (e.g. only certain operations like
  division/`Int.MIN/-1`, or only overflow encountered during the *original
  solve* rather than a later eval call), or it is effectively dead in
  normal evaluator usage. **Do not guess which** — mt-062 should implement
  silent wraparound (matching every probe here) and revisit only if a real
  model surfaces the marker.
- **`ErrorSyntax("The input does not correspond to an Alloy expression.")`**
  (`scratchpad/src794/CompModule.java:986-987`, the `m.funcs.size()==0`
  branch) was not independently exercised — every malformed-input probe
  attempted (garbage tokens, a comment-only line) hit the generic
  "unexpected token" parser error first (E-15-E-20). It's unclear what
  input, if any, reaches this specific branch through the real console
  (blank input never reaches the parser at all — filtered in
  `OurConsole.do_command` itself). Low priority: this is a source-only,
  unreachable-in-practice message as far as these probes show.
- **The `HigherOrderDeclException → ErrorType("Higher-order quantification
  is not allowed in the evaluator.")` mapping (§0 step 10)** is pinned from
  bytecode/mechanism only — not independently exercised with a real
  higher-order-quantification input this pass. The mechanism is
  unambiguous (a single catch-and-rewrap in `SimpleGUI$6.compute`), so this
  is recorded as source/bytecode-pinned rather than jar-behavior-verified;
  low risk given how mechanical the rewrap is, but flagged honestly.
- **§4 (temporal/`var`) is deliberately shallow** per this task's scope —
  `setCurrentState`'s call sites (how the GUI drives `current` as a user
  steps a trace), `mintrace`/`maxtrace`/loop-state validity bounds on
  `state`, and whether temporal operators (`always`, `until`, `Prime`) are
  even legal evaluator input, are all open — this is explicitly deferred to
  Rung 6, not a gap in this pass.
- **The exact loop/shape that produces the `-1, -2, ..., -8, 0, ..., 7`
  int-atom sub-order** (§3) inside `A4SolutionReader`'s universe
  reconstruction was not tracked down to a specific bytecode loop — the
  *fact* is solidly pinned (reproduced identically across four different
  models, E-03/E-05/E-45/E-46), but the *mechanism producing it* inside
  `A4SolutionReader`/Kodkod's `TupleFactory` was not chased past
  confirming it happens (not present in the written XML as explicit
  per-atom entries — it's the reader's own reconstruction, keyed only off
  `bitwidth`). Not needed for mt-062 (§5 already recommends not replicating
  this order), but flagged in case a future task needs the "why."
