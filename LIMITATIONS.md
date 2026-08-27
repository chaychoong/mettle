# Limitations

This file lists what mettle cannot do today. It also lists every difference from the reference Alloy Analyzer 6.2.0 jar.

The file describes the present state only. Every listed gap is open today. Closed gaps leave this file, and git history keeps the record.

Two rules apply throughout:

- mettle never answers a command that it cannot translate. An unsupported construct produces a typed error.
- mettle never rejects a model that the Alloy jar accepts.

Almost no entry can change a SAT or UNSAT verdict. Each entry states its effect. See [docs/STATE.md](docs/STATE.md) for current measured agreement.

## Commands mettle cannot run

### Commands beyond the sweep budgets

`fullsub2.als[0]` answers UNSAT and agrees with the jar. It uses about 5.19M conflicts and takes 27 minutes.

Run it with:

```console
backend-instrument --rows - --conflicts 8000000 --wall 3000
```

The default budget stays unchanged. One extra agreement costs about 2.5x the sweep wall time. See [docs/adr/0017-gauge-default-budgets-paired-frontier.md](docs/adr/0017-gauge-default-budgets-paired-frontier.md).

**SAT/UNSAT effect:** No. A larger budget produces the same UNSAT verdict as the jar.

`correctChord.als[13]` has no reference verdict. The jar times out on that file at any budget.

**SAT/UNSAT effect:** No. Neither side supplies a verdict to compare.

### Commands the jar also refuses

A higher-order declaration that cannot be skolemized returns the jar's own HigherOrderDeclException message. This shape covers 4 corpus commands.

**SAT/UNSAT effect:** No. Both engines refuse the command with the same message.

Unbounded model checking (`for 1.. steps`) returns the jar's own refusal text. This shape covers 2 corpus commands.

**SAT/UNSAT effect:** No. Both engines refuse the command with the same text.

## Models mettle accepts that Alloy rejects

mettle and the jar agree in both directions on all 150,891 alloy4fun submissions. Agreement is 100.0000%, measured 2026-08-25.

Three known shapes remain. None appears in any corpus.

### Post-colon `disj`

A post-colon `disj` on a quantifier or run-pred declaration (`x: disj e`) causes a resolve error in the jar. mettle accepts it, then reports that it cannot run the command.

Measured incidence is zero. The gap is open.

**SAT/UNSAT effect:** No. mettle does not answer the command.

### Receiver-style call of a zero-argument predicate

A receiver-style call such as `H.s.noDuplicates` causes a type error in the jar. mettle accepts it.

Measured incidence is zero. The gap is open.

**SAT/UNSAT effect:** No.

### Defined field on a `one` sig

This deliberate defer was decided 2026-08-26. A user-written defined field on a `one` sig crashes the jar. mettle answers it.

The crash gate is probe-mapped across 9 cells in `scratchpad/probe/mt135/`. The owning sig is `one`, the field uses `=`, and the bound is sim-able.

A sim-able bound is a sig, `univ`, or a `+`/`->` combination. A sim-able combination throws UnsupportedOperationException from A4Solution.addSymbolicBound. A bare sig StackOverflowErrors in PardinusBounds$SymbolicStructures.transitiveDeps.

The crash occurs during solving and is unconditional for each command. The jar exposes a raw stack trace. It gives no diagnostic.

The nearby shapes do not crash:

- `g = none` gets the same clean resolve-time rejection and message on both sides.
- A defined field on a non-`one` sig solves on both sides.
- A defined field whose bound references another field solves on both sides.

mettle answers every crash-family cell. The jar crash is accidental. Designed refusals form a separate family.

This case belongs to the family where mettle answers and the jar gives no verdict. Clean-diagnostic parity is a separate family.

Incidence is zero in all three corpora. The measurement uses jar 6.2.0.

**SAT/UNSAT effect:** No. The jar produces no verdict.

## Overflow guard corners

These entries describe differences under the default noOverflow mode. They have zero incidence in both corpora and come from hand-written probe models.

This is the only group that can change a verdict, on a synthetic model. Measurements are in sections 10.7e through 10.7l of [docs/reference/alloy6-translation.md](docs/reference/alloy6-translation.md).

### Translation-class cache

mettle reproduces the jar's polarity-blind formula reuse with translation classes. A formula-valued `let` and a zero-parameter pred use the first visit's overflow guard.

See [docs/adr/0029-polarity-blind-translation-cache.md](docs/adr/0029-polarity-blind-translation-cache.md) and LEDGER-017.

Three corners remain deliberately open. All have zero incidence.

1. The temporal path keeps per-use translation. The jar's temporal cache lineage is unprobed.
2. First-visit order can differ when the jar's short-circuit constant folding visits conjuncts in another order. Every probe cell matches.
3. A REPL query answers polarity-correctly where the jar's evaluator would reuse.

Fragments carry no class table. At the prompt, `let p = ... | p or (not p)` is honestly UNSAT-shaped. The solved command above it still matches the jar.

**SAT/UNSAT effect:** Yes. This overflow-guard group can change a verdict on a synthetic model.

### Nearby unverified corners

Three nearby corners remain unverified.

- A cast inside a Card or sum operand adds no comparison-level guard flag. This comes from source reading, without a probe.
- A cast in a quantifier declaration bound gets emptiness semantics but no declaration-level guard.
- Casts under `&` or `-` appear to guard like unions. This comes from source reading, without probe confirmation.

**SAT/UNSAT effect:** Yes. This overflow-guard group can change a verdict on a synthetic model.

## Differences chosen on purpose

Each difference makes mettle safer than the reference. None can change a verdict on a real model.

### Very long flat operator chains

mettle rejects very long flat operator chains. Root-to-leaf AST path depth stops at 768 with a typed `TooDeep` error.

Without this bound, a plain `.als` file crashed the process. The jar throws a raw StackOverflowError at 5,000 chained terms. It supplies no correct reference behavior to copy.

The longest chain in 150,891 alloy4fun codes has 113 terms. The longest in the vendored corpus has 8.

An AST built through the als-syntax API without the parser remains unbounded. Printing such a tree can overflow the stack in a release build.

Code records this risk as print::MAX_SAFE_PRINT_PATH. The iterative printer rewrite was evaluated and rejected in [docs/adr/0022-recursion-depth-safety-flat-chains.md](docs/adr/0022-recursion-depth-safety-flat-chains.md).

**SAT/UNSAT effect:** No, on any observed input. Real chains stay far below the bound.

### Deeply nested expressions

mettle returns a typed `TooDeep` error at 256 levels. The jar throws a raw StackOverflowError.

See section 3 of [docs/reference/fuzzing.md](docs/reference/fuzzing.md).

**SAT/UNSAT effect:** No, on any observed input. Real nesting stays far below the bound.

### Unterminated block comments

An unterminated block comment is an error. The reference lexer silently ignores a `/*` that never closes. Well-formed input cannot reach this difference.

**SAT/UNSAT effect:** No.

### Parse-error positions

Two parse-error families differ from the jar. Both engines reject the input. Only the caret moves.

Across the 14,560 alloy4fun codes that both reject at syntax level, 99.79% use the jar's exact line and column. See section 5 of [docs/reference/alloy4fun-error-pass.md](docs/reference/alloy4fun-error-pass.md).

Ten hand-written malformed models were re-measured 2026-08-25. Eight positions match exactly. Both misses belong to one family, a brace-introduced declaration list.

For `some x: A | x in {a, b }`, the jar consumes the comma-separated name list. It reports at the `}`, column 31.

mettle treats the brace as a block after the first name. It reports at the comma, column 27, and names the expected construct.

Matching needs lookahead in the block-versus-comprehension decision. This is the one parser choice pinned by the alloy4fun accept-reject differential.

In the second family, mettle lexes the full file before parsing. A stray character on line 3 preempts a parse error on line 2 that the jar reports first.

A stray character alone lands at the jar's exact position.

**SAT/UNSAT effect:** No. Both engines reject the input.

### Identifier characters

mettle uses Rust's Unicode classes for identifiers. Java's classes are slightly wider. Only exotic non-ASCII identifiers differ.

One alloy4fun submission used the euro sign as an operand. Java treats a currency symbol as an identifier character. mettle does not.

mettle reports a lexing error. The jar reports a type error. See [docs/reference/alloy4fun-error-pass.md](docs/reference/alloy4fun-error-pass.md).

**SAT/UNSAT effect:** No. Both engines reject the file.

### One-state temporal commands

mettle answers one-state temporal commands. The jar crashes with a null pointer error when a `for 1 steps` command folds to a constant.

The jar answers the remaining commands. mettle answers all of them and conforms where the jar answers.

The upstream report is [AlloyTools issue 350](https://github.com/AlloyTools/org.alloytools.alloy/issues/350). See LEDGER-015 in [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md).

**SAT/UNSAT effect:** No. mettle conforms wherever the jar produces a verdict.

## Bounded temporal solving

### Meaning of UNSAT

For a bounded temporal command, UNSAT means no instance exists within the steps bound. It gives no claim beyond that bound.

Raising the bound can change the answer. `mettle exec` states the bound in its verdict line:

```text
VALID (no counterexample within 10 steps)
```

**SAT/UNSAT effect:** No. The verdict states the bounded semantics directly.

### Unbounded model checking

Unbounded model checking is out of scope, as it is for the jar out of the box. The bounded reference engine refuses `for 1.. steps` before solving.

mettle returns the same message. The unbounded path needs the external electrod solver. The contract could not vouch for its semantics.

**SAT/UNSAT effect:** No. Neither engine produces a verdict through the bounded path.

### Open exact ranges

`for exactly N.. steps` is unverified. Probes cover only `exactly N..M`. The jar discards the written upper bound there, and mettle matches.

On an open range, `exactly` is still ignored. This shape needs its own probe cell.

**SAT/UNSAT effect:** No. No measured verdict difference is known.

### Unused temporal macros

An unused macro that contains a temporal operator is treated as non-temporal. mettle follows a used macro into its body when classifying a command.

This matches the jar. An unused macro never reaches the jar's fact set or command body, so the engines should agree.

Only used shapes were probed. [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md) records the unused case as an assumption.

**SAT/UNSAT effect:** No. No measured verdict difference is known.

### Static-command evaluation

mettle's evaluator refuses temporal operators on a static command. The jar evaluates them over its degenerate one-state trace and answers correctly.

mettle reports that it cannot evaluate the expression. This feature is missing. mettle gives no wrong answer.

**SAT/UNSAT effect:** No. The difference affects evaluation after solving.

## Counting and enumeration

The conformance test compares verdicts. It compares instance counts separately. See [docs/adr/0002-conformance-oracle.md](docs/adr/0002-conformance-oracle.md).

Every entry in this section affects counts or presentation only. None affects a verdict.

### Abstract ordered sigs with free children

An abstract ordered sig with free children counts differently at symmetry 0. The jar mints atoms per child.

It treats each atom-to-child labelling as a separate instance. Its count is n! times mettle's count.

The counts are 9216 against 384 at `for 4 A`. mettle mints canonical parent atoms. Cases with a determinate population count exactly.

**SAT/UNSAT effect:** No. Only the instance count differs.

### Plain-product arrow declarations

mettle reads a plain-product arrow quantifier declaration as first-order. For `some p: A -> univ`, the jar treats p as any sub-relation.

mettle treats p as one pair. The counting test skips this shape.

**SAT/UNSAT effect:** No. Verdicts agree. Counts differ.

### Temporal counts

Temporal counts are relative to a configuration. The jar's plain "next trace" stays within the static configuration from its first solve.

Its count covers traces from its own first configuration. mettle's count covers traces from mettle's first configuration.

Exact parity is unreachable when the configuration space has more than one member. mettle reproduces the algorithm exactly. The test reports a typed skip.

See LEDGER-014 in [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md).

**SAT/UNSAT effect:** No. Only the count differs.

### Enumeration order

Enumeration is exact. Order comes from the solver. Every distinct instance appears once. The sequence ends at a true UNSAT.

CaDiCaL determines which instance appears first.

**SAT/UNSAT effect:** No. Enumeration remains exact.

### Per-state symmetry breaking

mettle groups a relation's state copies together. The jar groups a state's relations together.

Either fixed bit order gives a sound lex-leader predicate. Only the surviving isomorphic representative changes.

**SAT/UNSAT effect:** No. Only the representative changes.

## Names, order and text

mettle prints the same sets as the jar, with its own spelling and order. See LEDGER-012 in [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md).

The conformance test compares none of these details.

### Tuple order

mettle uses solve order: sig atoms in declaration order, then ascending integers, then strings.

The reference console prints strings first, then integers in its XML reader's order, then sig atoms. The sets are equal.

A relation containing `A + 1 + 3 + "zz" + "aa"` was re-measured 2026-08-25. The reference console renders `{"aa", "zz", 1, 3, A$0, A$1}`.

mettle renders `{A$0, A$1, 1, 3, "aa", "zz"}`. Byte parity would require the console's serialize-and-reparse round trip and its reordering side effect.

**SAT/UNSAT effect:** No. The sets are equal.

### Atom labels

Atom labels differ for a non-exact subsig. mettle mints subsig atoms from the parent's pool.

Thus, `sig B extends A` yields `A$2` in mettle and `B$0` in the jar.

This was re-measured 2026-08-25 with one atom each. The label was the only difference in the complete instance XML.

Bounds construction builds the pool before any writer sees it. Bounds construction determines the label.

**SAT/UNSAT effect:** No. Only the atom label differs.

### Trace rendering

Trace rendering copies the reference shape. It uses the jar's `---Trace---` header, per-state blocks, and loop marker.

Lines inside each block use mettle's instance rendering. The test a_forced_trace_renders_state_by_state_with_the_loop_marked pins the frame line by line.

The test is in `crates/mettle/tests/exec.rs` and uses a captured jar trace.

**SAT/UNSAT effect:** No. Only rendering differs.

### Error text

mettle uses its own caret diagnostics. Two messages come from the reference because they state evaluator rules.

They cover the higher-order quantification refusal and the missing string literal. mettle emits both verbatim, and separate tests pin them.

**SAT/UNSAT effect:** No. Only diagnostic text differs.

## Instance XML export

`mettle exec <file.als> --xml <PATH>` writes the reference writer's structure exactly. The jar's reader accepted every file tested, 30 of 30.

For a determinate instance, the complete document is byte-identical. This includes escaping and lazy ID numbering.

The differences below do not affect a reader. See [docs/reference/alloy6-instance-xml.md](docs/reference/alloy6-instance-xml.md).

### `<source>` entries

mettle writes the model path supplied on the command line. The jar writes an absolute path. Given an absolute path, mettle writes the same bytes.

mettle names embedded modules `<stdlib>/util/integer.als`. The jar uses `/$alloy4$/models/util/integer.als`.

mettle writes embedded modules after user files. The jar places util/integer directly after the root.

These differences remain. mettle's standard library is clean-room text, so embedded content= cannot match the jar's.

The jar path also names a file that mettle does not ship. See [docs/adr/0006-licensing-posture.md](docs/adr/0006-licensing-posture.md).

**SAT/UNSAT effect:** No. The differences do not affect an XML reader.

### Range and increment scope text

A range or increment scope records its lower endpoint. For `for 3 but 1..3 P`, mettle writes `1 P` in the command= attribute.

The jar writes `3 P`. Both engines solve at the low end and agree.

**SAT/UNSAT effect:** No. Only recorded text differs.

### Skolem `<types>` columns

mettle gets Skolem `<types>` columns from the solver bound. The jar gets them from a declared type.

See LEDGER-013 in [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md).

**SAT/UNSAT effect:** No. The difference does not affect an XML reader.

### Metamodel output

writeMetamodel (metamodel="yes") is a separate jar entry point. It never appears with a solved instance. mettle does not implement it.

**SAT/UNSAT effect:** No. It is separate from solved-instance output.

## The evaluator REPL

`mettle exec --repl` and `--eval <EXPR>` evaluate expressions against one solved instance. The contract is in [docs/reference/alloy6-evaluator.md](docs/reference/alloy6-evaluator.md).

Rendering shapes match the reference.

### Registered names

Only sig atoms are registered as names. An integer atom is named `-3`, and a string atom is named `"hi"`.

Neither form lexes as an identifier, so neither was reachable by name. Arithmetic and string literals reach them, as in the reference.

Every skolem name minted by the solve is registered.

**SAT/UNSAT effect:** No. This affects evaluator name lookup after solving.

### Names for unused atoms

Every sig atom in the universe has a name, including atoms that no sig holds. The reference display renames these atoms to unused0.

mettle keeps the minting sig's name. Thus, `A$2` names the atom even when `A = {A$0}`.

The accepted reference evaluator label was never pinned. This behavior is unverified.

**SAT/UNSAT effect:** No. This affects evaluator name lookup after solving.

### Under-applied calls

An under-applied predicate or function gets a generic unresolved-name message. The reference explains the parameter list.

The answer is correct. The message is worse.

**SAT/UNSAT effect:** No. Only the diagnostic differs.

### Unreferenced string literals

A string literal absent from the command has no atom in that command's universe. It cannot be evaluated.

The reference behaves the same way.

**SAT/UNSAT effect:** No. Both evaluators have the same limit.

### Prompt features

The prompt has no enumeration and no line editing. It has no next-instance navigation, history, or readline.

The read loop is hand-written, and no dependency was taken. `:state N` is the only trace control for a temporal command.

**SAT/UNSAT effect:** No. These are prompt features after solving.

## `mettle serve`

`mettle serve` solves one command and serves the Sterling provider protocol on 127.0.0.1.

The reference jar ships no Sterling. These entries are not conformance questions. See Decision 2 in [docs/adr/0016-rung5-remainder-serve-xml-packaging.md](docs/adr/0016-rung5-remainder-serve-xml-packaging.md).

### Views

Views are not customizable. mettle provides a graph view and a table view. Both are pure functions of the instance.

There is no sig projection, hand placement, saved layout, or user theme beyond system light/dark. Per-relation controls cover only the builtin-and-private toggle that the reference visualizer also has.

Edge labels use estimated character widths. The layout does not measure rendered text, so a dense bundle can overlap.

**SAT/UNSAT effect:** No. These limits affect visualization only.

### Enumeration after a fork

One enumeration corner is unprobed. After a fork, "next trace" stays within the fork's trace length.

Budget or capacity exhaustion during enumeration produces a typed stop. mettle never repeats or invents a trace.

**SAT/UNSAT effect:** No. This affects enumeration after solving.

### External Sterling loop points

An external Sterling loses the loop point. mettle serves the jar's `looplength` dialect. The sterling-ts parser reads only `backloop`.

mettle's frontend reads the jar dialect. The issue affects only interoperation with an upstream Sterling build.

**SAT/UNSAT effect:** No. This affects trace display only.

### Stale datum IDs

mettle refuses a stale datumId and states which instance is current. Forge answers against its current instance instead.

That Forge behavior can answer about a different instance, which is wrong.

**SAT/UNSAT effect:** No. This concerns provider queries after solving.

### Solve options

`mettle serve` exposes almost no solve options. `--allow-overflow`, `--conflicts` and `--encode-budget` are exec options. Serve uses their defaults.

`--solver` is the exception. A visualization must state which backend supplied its answer.

**SAT/UNSAT effect:** No. Serve uses the documented defaults.

### Sessions and shutdown

The server supports one session and one command. Browser tabs share one solved session behind a mutex.

A multi-command file needs `--command`. The server stops on Ctrl-C. The protocol has no shutdown message.

**SAT/UNSAT effect:** No. These limits concern session control.

## The solver

Since [ADR-0027](docs/adr/0027-cadical-only-solver.md), mettle uses CaDiCaL 1.9.5. It uses the vendored MIT binding in `vendor/cadical`.

`--solver` remains the plugin interface. It resolves only `cadical`.

### C++ toolchain

Every build needs a C++ toolchain because the backend compiles unconditionally.

Release artifacts, the container image, and the nix package include about 100 vendored C++ sources. They link libstdc++.

The Dockerfile installs a toolchain. nix's stdenv provides one.

**SAT/UNSAT effect:** No. This is a build requirement.

### Determinism

Determinism applies to a fixed build. A fixed CaDiCaL build answers identically on every run.

CaDiCaL's restart policy compares floating-point averages of clause glue. Cross-architecture divergence was therefore possible in principle.

`.cargo/config.toml` sets `-ffp-contract=off` for the vendored C++. The cross-target battery measured full byte-identity on all four release targets, twice.

From v0.1.2, that identity is a hard release-tag gate. The guarantee covers the pinned and tested builds only.

**SAT/UNSAT effect:** No. No measured effect exists for the pinned and tested builds.

### x86_64 macOS horizon

The x86_64 macOS target runs on macos-15-intel. This is GitHub's last Intel macOS runner image, and it retires in autumn 2027.

**SAT/UNSAT effect:** No. This concerns release infrastructure.

### DRAT certificates

`backend-instrument --certify` makes CaDiCaL log a proof for an UNSAT verdict. drat-trim checks it against the exact CNF solved.

This proves that the CNF is unsatisfiable. The certificate gives no proof that the CNF correctly encodes the Alloy command.

The evaluator self-check covers the encoding for SAT answers. The jar covers it for both verdicts.

**SAT/UNSAT effect:** No. This entry states the certificate's proof boundary.

### Conflict budgets

`--conflicts` caps effort for each solve. The solver remains usable after reaching the cap.

There is no decision-count budget.

**SAT/UNSAT effect:** No. Budget exhaustion produces no verdict.

## Solve budgets and capacity

### `mettle exec` budgets

`mettle exec` applies no solve budgets, by design. The reference runs a command until it answers, and exec is the drop-in surface.

A wide steps range on a large model can take a long time. `leader.als` takes about 11 minutes.

`--conflicts` and `--encode-budget` enable budgets. The conformance sweep owns budgeted runs.

**SAT/UNSAT effect:** No. The default waits for an answer.

### Budget exhaustion

A budgeted command that runs out reports a typed defer. It never reports a wrong verdict.

Every such command is solvable with a larger budget.

**SAT/UNSAT effect:** No. Exhaustion produces a typed defer and no verdict.

## Modules and the standard library

### Embedded modules

Only `util/*` is embedded as a last-resort module fallback. The jar also serves its bundled `models/*` files this way.

A model that opens a non-util jar-embedded module fails to load in mettle.

This had negligible effect in the alloy4fun run. The only cases were 6 codes whose jar rejection was a genuine parse error.

**SAT/UNSAT effect:** No. The known cases are rejected by the jar.

### `util/ordering` exact pinning

`util/ordering` exact pinning covers childless and enum ordered sigs only. An ordered sig with children uses the hand-built pred/totalOrder formula.

Verdicts and counts are pinned to the jar in both cases. See LEDGER-004 in [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md).

**SAT/UNSAT effect:** No. Verdicts match.

### `util/ordering` detection corners

Two corners remain unverified.

A module fact using explicit field qualification such as `Ord.First` is deliberately not matched. The jar may pin there.

This shape has zero corpus incidence, so mettle under-approximates it.

The pred/totalOrder keyword does not pin a genuinely non-exact element sig. The jar's behavior there was not probed.

**SAT/UNSAT effect:** No. No measured verdict difference is known.

### `fun/add` index arithmetic

`fun/add` index arithmetic could wrap. In the `util/sequence` copy, append and subseq can wrap their index arithmetic.

This can occur at a SeqIdx scope past about 4 under bitwidth 4. The corner is pre-existing, unprobed, and unverified.

**SAT/UNSAT effect:** No. No measured verdict difference is known.

## Internal differences that cannot change an answer

### Reflexive padding

mettle omits the reference's reflexive `r = r` padding. The jar uses it to keep unreferenced relations alive for Kodkod's solver.

The padding has no meaning.

**SAT/UNSAT effect:** No.

### `Int/min` and `Int/max`

mettle does not bind the `Int/min` and `Int/max` relations. The jar binds them but never references them.

`fun/min` and `fun/max` lower as integer constants.

**SAT/UNSAT effect:** No.

### Arrow field bounds

mettle omits the jar's redundant per-column membership constraints on arrow field bounds at every depth.

Top-level membership entails these constraints.

**SAT/UNSAT effect:** No.

## Permanent non-goals for v1

### Native GUI

v1 has no native GUI. It provides Sterling and the CLI only.

**SAT/UNSAT effect:** No.

### Unbounded model checking

v1 has no unbounded model checking. Temporal solving is bounded.

**SAT/UNSAT effect:** No. mettle refuses unbounded commands.

### Obscure syntax corners

v1 does not cover obscure syntax corners beyond those tracked in this file.

**SAT/UNSAT effect:** No. Unsupported constructs produce a typed error.

## Maintenance

Every construct that parses but cannot be solved appears in this file. Each fails with a precise message.

mettle never answers wrongly. When a gap closes, its entry leaves this file. The scorecard in [docs/STATE.md](docs/STATE.md) records the new agreement level.
