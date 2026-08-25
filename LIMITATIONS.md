# Limitations

This file lists what mettle cannot do today, and every place where mettle behaves
differently from the reference Alloy 6.2.0 jar. It describes the present state.
Git history holds the record of how each gap was found and closed.

Two rules hold everywhere below. mettle never answers a command it cannot
translate: an unsupported construct produces a typed error that says so. And
mettle never rejects a model the jar accepts. Almost nothing in this file can
change a SAT or UNSAT verdict; every entry says whether it can.

The zero-gap campaign ([ADR-0028](docs/adr/0028-zero-gap-campaign.md)) is
running now and covers most of the remaining correctness items. Those entries
name the bead that is closing them.

Current measured agreement with the jar is in [docs/STATE.md](docs/STATE.md).

## Commands mettle cannot run

- **The `Sig$` metamodel.** A model that names a meta sig or meta field
  (`Vertex$.subfields`) gets a message saying mettle cannot run the command. Two
  corpus commands are affected, `hc7.als[0]` and `einstein-wikipedia.als[0]`.
  The jar answers both. The feature needs a synthesis phase that mints a meta sig
  per user sig, puts those atoms in the universe, and expands quantifiers over
  them at resolve time. Being built as mt-107.
- **Two commands run past the sweep budgets.** `fullsub2.als[0]` answers UNSAT,
  agreeing with the jar, at about 5.19M conflicts and 27 minutes of wall time;
  run it with `backend-instrument --rows - --conflicts 8000000 --wall 3000`. The
  default budget is not raised for it, because one extra agreement costs about
  2.5 times the sweep wall time ([ADR-0017](docs/adr/0017-gauge-default-budgets-paired-frontier.md)).
  `correctChord.als[13]` has no answer to agree with: the jar times out on that
  file at any budget.
- **Two shapes where the jar also refuses.** A higher-order declaration that
  cannot be skolemized returns the jar's own `HigherOrderDeclException` message
  (4 corpus commands). Unbounded model checking (`for 1.. steps`) returns the
  jar's own refusal text (2 corpus commands). These match the reference exactly.

## Models mettle accepts that Alloy rejects

Over the 150,891 alloy4fun submissions, mettle and the jar now agree on every
verdict: mettle rejects nothing the jar accepts and accepts nothing the jar
rejects (100.0000% agreement, measured 2026-08-25 after mt-107 phase P2).
Two known shapes remain where mettle is more accepting than the jar, and
neither appears in any corpus.

- **Two shapes with no measured incidence.** A post-colon `disj` on a quantifier
  or run-pred declaration (`x: disj e`) is a resolve error in the jar; mettle
  accepts it and then reports that it cannot run the command. A receiver-style
  call of a zero-argument predicate (`H.s.noDuplicates`) is a type error in the
  jar; mettle accepts it. Neither appears in either corpus. Open.

## Overflow guard corners

These are the places where mettle's overflow guard differs from the jar's under
the default `noOverflow` mode. All have zero incidence in both corpora and were
found with hand-written probe models. They are the one group in this file that
can give a different verdict, on a synthetic model. The union and short-circuit
shedding family closed at mt-130 (2026-08-25): the mt-129 wave pinned the jar's
mechanism from the Kodkod source, and mettle now folds constant emptiness the
same way, verified on all 137 probe cells with a byte-identical corpus sweep.
Measurements are in
[docs/reference/alloy6-translation.md](docs/reference/alloy6-translation.md)
§10.7e through §10.7k and `scratchpad/probe/mt129/NOTES.md`.

- **`toInt` throws away a cardinality (mt-127).** When the operand of `#` is
  itself an `Int[·]` cast and an integer reader consumes the result, the jar
  reads the operand's raw integer and discards the count. `#(plus[3,4]) >= 7` is
  SAT in the jar (it reads 7) and UNSAT in mettle (it reads 1). Under a set
  reader (`=`, `in`) both sides treat `#` as an ordinary cardinality. The fix
  needs the integer-comparison gate re-keyed on the jar's literal-cast test
  first; the direct patch was measured and it moved the divergences instead of
  closing them.
- **An `int[·]` in an if-then-else branch (mt-128).** Alloy's resolver re-wraps a
  surface `int[e]` as `Int[int[e]]`, which makes the branch a set, and it does
  not re-wrap `#e` in the same position. Both carry Alloy type `{Int}`, so the
  type system does not tell them apart. mettle carries no marker for the re-wrap.
  The fix threads the resolver's marker through to the sort decision.
- **A `let` binding an integer value is read as relational (mt-128).** The sort
  of an if-then-else is read off the then branch before lowering descends into
  it, so a `let` binder in that branch is not yet in scope and its name reads as
  relational. The fix threads a substitution environment through the sort
  decision, the shape the jar's own `visit(ExprLet)` uses.
- **Three nearby corners, kept as unverified.** A cast nested inside a `Card` or
  `sum` operand contributes no comparison-level guard flag (the jar merges those
  conditions transitively; this comes from reading the source and no probe has confirmed it). A cast in a quantifier
  declaration bound gets the emptiness semantics but not the declaration-level
  guard. Casts nested under `&` or `-` are source-read as guarding like unions
  and have not been probe-confirmed.

## Differences we chose on purpose

Each of these is a place where mettle is safer than the reference. None of them
can change a verdict on a real model.

- **Very long flat operator chains are rejected instead of parsed.** The parser
  bounds root-to-leaf AST path depth at 768 and reports a typed `TooDeep` error.
  Without the bound, a plain `.als` file crashed the process. The jar is not safe
  here either: it throws a raw `StackOverflowError` at 5,000 chained terms, so
  there is no correct reference behaviour to copy. Real input is far below the
  bound: the longest chain in the 150,891 alloy4fun codes is 113 terms, and the
  longest in the vendored corpus is 8. See
  [ADR-0022](docs/adr/0022-recursion-depth-safety-flat-chains.md).
  One residual: an AST built through the `als-syntax` API without going through
  the parser is not bounded, so printing or dumping such a tree can still
  overflow the stack in a release build. That is documented in code as
  `print::MAX_SAFE_PRINT_PATH`. Closing it needs the iterative printer rewrite,
  which ADR-0022 evaluated and rejected.
- **Deeply nested expressions give a typed error.** The parser guards recursion
  depth at 256 levels and reports `TooDeep`. The jar throws a raw
  `StackOverflowError`. See [docs/reference/fuzzing.md](docs/reference/fuzzing.md) §3.
- **An unterminated block comment is an error.** The reference lexer silently
  ignores a `/*` that never closes. Well-formed input cannot reach this.
- **Two parse-error positions differ from the jar's.** Both engines reject the
  file either way; only the caret moves. Over the 14,560 alloy4fun codes both
  reject at the syntax level, 99.79% land on the jar's exact line and column
  ([docs/reference/alloy4fun-error-pass.md](docs/reference/alloy4fun-error-pass.md)
  §5). Ten hand-written malformed models re-measured against the jar on
  2026-08-25 put eight on the exact position and both misses in one family, a
  brace-introduced declaration list. On `some x: A | x in {a, b }` the jar
  consumes the whole comma-separated name list and reports at the `}`, column
  31; mettle decides the brace opens a block once the first name is in and
  reports at the comma, column 27, naming the construct it wanted. Matching
  would mean adding lookahead to the block-versus-comprehension decision, which
  is the one parser choice the alloy4fun accept-reject differential pins. The
  second family is a different line: mettle lexes the whole file before parsing,
  so a stray character on line 3 preempts a parse error on line 2 that the jar
  reports first. A stray character on its own lands on the jar's exact position.
- **Identifier characters follow Rust's Unicode classes.** Java's classes are
  slightly wider. Only
  exotic non-ASCII identifiers can differ. One alloy4fun submission used `€` as
  an operand: Java counts a currency symbol as an identifier character and mettle
  does not, so mettle reports a lexing error where the jar reports a type error.
  Both reject the file. See
  [docs/reference/alloy4fun-error-pass.md](docs/reference/alloy4fun-error-pass.md).
- **One-state temporal commands are answered.** The jar crashes with a null
  pointer error on the subset of `for 1 steps` commands whose translation folds
  to a constant, and answers the rest. mettle answers all of them, and conforms
  wherever the jar answers. The crash is filed upstream as
  [AlloyTools#350](https://github.com/AlloyTools/org.alloytools.alloy/issues/350).
  See [LEDGER-015](SEMANTICS_LEDGER.md).

## Bounded temporal solving

- **UNSAT means "no instance within the `steps` bound".** It does not mean the
  assertion holds. Raising the bound can flip the answer. `mettle exec` says so
  in the verdict line: `VALID (no counterexample within 10 steps)`.
- **Unbounded model checking is out of scope,** as it is for the jar out of the
  box. The reference's bounded engine refuses `for 1.. steps` before solving, and
  mettle raises the same message. Reaching the unbounded path needs the external
  `electrod` solver, whose semantics the contract could not vouch for.
- **`for exactly N.. steps` is unverified.** The probes covered only the bounded
  form `exactly N..M`, where the jar discards the written upper bound and mettle
  now matches it. On an open range, `exactly` is still ignored. This needs its
  own probe cell.
- **An unused macro holding a temporal operator is treated as non-temporal.**
  mettle follows a used macro into its body when deciding whether a command is
  temporal, matching the jar. An unused macro never reaches the jar's fact set or
  command body either, so the two should agree, but only the used shapes were
  probed. Kept as an assumption, recorded in
  [SEMANTICS_LEDGER.md](SEMANTICS_LEDGER.md).
- **A static command's evaluator refuses temporal operators.** The jar evaluates
  them over its degenerate one-state trace and answers correctly. mettle reports
  that it cannot evaluate them. This is a missing feature. mettle gives no wrong
  answer here.

## Counting and enumeration

The conformance test compares verdicts. Instance counts are compared separately
([ADR-0002](docs/adr/0002-conformance-oracle.md)), and these entries
affect counts only. A verdict never moves.

- **An abstract ordered sig with free children counts differently at symmetry 0.**
  The jar mints atoms per child and counts each atom-to-child labelling as its own
  instance, so its count is `n!` times mettle's (9216 against 384 at `for 4 A`).
  mettle mints canonical parent atoms. Cases with a determinate population count
  exactly.
- **A plain-product arrow quantifier declaration is read first-order.** For
  `some p: A -> univ`, the jar reads `p` as any sub-relation and mettle reads it
  as one pair. Verdicts agree; the counts differ. The counting test skips this
  shape.
- **Temporal counts are relative to a configuration.** The jar's plain "next
  trace" never leaves the static configuration its first solve landed on, so its
  count is the traces of its own first configuration and mettle's is the traces
  of mettle's. On a command whose configuration space has more than one member,
  exact parity is not reachable. mettle reproduces the algorithm exactly and the
  test reports such a disagreement as a typed skip. See
  [LEDGER-014](SEMANTICS_LEDGER.md).
- **Enumeration is exact; the order is the solver's.** Every distinct instance
  appears once and the sequence ends at a true UNSAT. Which instance or trace
  appears first comes from CaDiCaL.
- **Per-state symmetry breaking uses a different bit order.** mettle groups a
  relation's state copies together; the jar groups a state's relations together.
  Any fixed bit order is a sound lex-leader predicate, so this changes only which
  isomorphic representative survives.

## Names, order and text

mettle prints the same sets as the jar, with its own spelling and order
([LEDGER-012](SEMANTICS_LEDGER.md)). None of this is compared by the conformance
test.

- **Tuple order is mettle's solve order.** For a value spanning several atom
  classes, mettle prints sig atoms in declaration order, then integers ascending,
  then strings. The reference console prints strings first, then integers in its
  XML reader's order, then sig atoms. The sets are the same. Re-measured against
  the jar on 2026-08-25: a relation holding `A + 1 + 3 + "zz" + "aa"` renders as
  `{"aa", "zz", 1, 3, A$0, A$1}` in the reference console and
  `{A$0, A$1, 1, 3, "aa", "zz"}` here. Matching the console byte for byte would
  mean copying its serialize-and-reparse round trip purely for the reordering
  side effect.
- **Atom labels for a non-exact subsig differ.** mettle mints subsig atoms from
  the parent's pool, so `sig B extends A` yields `A$2` where the jar yields
  `B$0`. Re-measured on 2026-08-25 with `sig A {} sig B extends A {}` forced to
  one atom each: that label is the only difference in the whole instance XML for
  that model. The pool is built during bounds construction, before any writer
  sees it, so the label is not a rendering choice.
- **Trace rendering copies the reference's shape.** The
  `---Trace---` header, the per-state blocks and the loop marker are the jar's.
  The lines inside a block are mettle's own instance rendering. The exact frame
  is pinned line by line against the jar's own captured trace by
  `a_forced_trace_renders_state_by_state_with_the_loop_marked` in
  `crates/mettle/tests/exec.rs`.
- **Error text is mettle's,** rendered as caret diagnostics. Two messages are the
  reference's, because each one states a rule about the evaluator: the
  higher-order quantification refusal and the missing string literal. Both are
  still emitted verbatim, each pinned by its own test.

## Instance XML export

`mettle exec <file.als> --xml <PATH>` writes the reference writer's structure
exactly, and the jar's own reader accepted every file it was given (30 of 30:
mt-071's 18, plus 12 more at mt-132). On a model whose instance is determinate,
the whole document is byte-identical to the jar's, escaping and lazy ID
numbering included. Four things still differ. None affects a reader. The schema
is in
[docs/reference/alloy6-instance-xml.md](docs/reference/alloy6-instance-xml.md).

- **`m<i>` index assignment inside an embedded stdlib module.** The set of macro
  skolems, and which module each one belongs to, match the jar exactly. Within a
  module both engines number in declaration order, so a model whose funcs are
  all its own agrees index for index. The one place they differ is
  `util/ordering`, because mettle's embedded copy declares `first, next, prev,
  last` and the jar's declares `first, last, prev, next`. Closing it means
  reordering mettle's own stdlib text.
- **`<source>` entries.** mettle writes the model path as given on the command
  line; the jar always resolves it to an absolute path. Given an absolute path
  mettle writes the same bytes. mettle also names its embedded modules
  `<stdlib>/util/integer.als` where the jar writes
  `/$alloy4$/models/util/integer.als`, and writes them after the user's files
  where the jar writes `util/integer` immediately after the root. Both of those
  stay. mettle's stdlib is a clean-room text
  ([ADR-0006](docs/adr/0006-licensing-posture.md)), so an embedded module's
  `content=` cannot match the jar's whatever the entry is called, and writing the
  jar's path would name a file mettle does not ship.
- **A range or increment scope records its lower endpoint.** `for 3 but 1..3 P`
  writes `1 P` in the `command=` attribute where the jar writes `3 P`. Both
  engines solve at the low end and agree on the verdict, so only the recorded
  text differs. The resolved command keeps the starting value alone, so the
  written upper endpoint never reaches the writer.
- **Skolem `<types>` columns** come from the solver bound. The jar derives them
  from a declared type. See [LEDGER-013](SEMANTICS_LEDGER.md).

`writeMetamodel` (`metamodel="yes"`) is a separate jar entry point that never
appears together with a solved instance, and mettle does not implement it.

## The evaluator REPL

`mettle exec --repl` and `--eval <EXPR>` evaluate against one solved instance,
built from the contract in
[docs/reference/alloy6-evaluator.md](docs/reference/alloy6-evaluator.md).
Rendering shapes match the reference. The remaining edges:

- **Only sig atoms are registered as names.** An integer atom is named `-3` and a
  string atom `"hi"`, and neither lexes as an identifier, so neither was ever
  reachable by name. They are reached as arithmetic and as string literals, as in
  the reference. Every skolem name the solve minted is registered too.
- **Every sig atom in the universe has a name, including atoms no sig holds.**
  The reference's instance display renames such atoms to `unused0`; mettle keeps
  the minting sig's name, so `A$2` names that atom even when `A = {A$0}`. Which
  label the reference's evaluator accepts for such an atom was never pinned.
  Unverified.
- **An under-applied predicate or function gets a generic message.** Typing
  `isEmpty` with no arguments is rejected, with a message about an unresolved
  name. The reference explains the parameter list instead. Correct answer, worse
  message.
- **A string literal the command never referenced cannot be evaluated.** It has
  no atom in that command's universe. The reference behaves the same way.
- **No enumeration and no line editing.** The prompt offers no "next instance"
  navigation, and the read loop is hand-rolled, with no history and no readline
  editing (no dependency was taken for it). `:state N` on a temporal command is
  the only trace control.

## mettle serve

`mettle serve` solves one command and answers the Sterling provider protocol on
`127.0.0.1`. The reference jar ships no Sterling, so nothing here is a
conformance question ([ADR-0016](docs/adr/0016-rung5-remainder-serve-xml-packaging.md)
Decision 2). What it does not do:

- **The views are not customizable.** There is a graph view and a table view,
  both drawn as a pure function of the instance. There is no projection over
  sigs, no hand-placement or saved layout, no user themes beyond following the
  system light and dark setting, and no per-relation show and hide beyond the
  builtin and `private` toggle the reference visualizer also has. Edge labels are
  spread using estimated character widths, because the layout never measures
  rendered text, so a dense bundle can still overlap.
- **One unprobed enumeration corner.** After a fork, "next trace" stays inside
  the fork's trace length. Budget or capacity exhaustion mid-enumeration is a
  typed stop. mettle never repeats a trace or invents one.
- **An external Sterling loses the loop point.** mettle serves the jar's
  `looplength` dialect. The `sterling-ts` parser reads `backloop` and never
  `looplength`. mettle's own frontend reads the jar dialect, so this affects only
  interop with an upstream Sterling build.
- **A stale `datumId` is refused.** Forge, the only other provider, answers about
  its current instance anyway. An answer about a different instance is a wrong
  answer, so mettle says which instance it is on instead.
- **Almost no solve knobs.** `--allow-overflow`, `--conflicts` and
  `--encode-budget` are `exec` options. `serve` always solves at their defaults.
  `--solver` is the exception, because which backend answered is not something a
  visualization should leave unstated.
- **One session, one command, no shutdown verb.** Several browser tabs share one
  solved session behind a mutex. A file with several commands needs `--command`.
  The server stops on Ctrl-C; the protocol has no shutdown message.

## The solver

Since [ADR-0027](docs/adr/0027-cadical-only-solver.md) the solver is CaDiCaL
1.9.5, through the vendored MIT binding in `vendor/cadical`. `--solver` remains
as the plugin interface, and `cadical` is the one name it resolves.

- **Every build needs a C++ toolchain.** The backend is compiled unconditionally,
  so release artifacts, the container image and the nix package all carry about
  100 vendored C++ sources and link libstdc++. The Dockerfile installs a
  toolchain and nix's stdenv already provides one.
- **Determinism is a property of a fixed build.** A fixed CaDiCaL build answers
  identically every run. CaDiCaL's restart policy compares floating-point
  averages of clause glue, so cross-architecture divergence was possible in
  principle. `.cargo/config.toml` pins `-ffp-contract=off` for the vendored C++,
  and the cross-target battery has measured full byte-identity on all four
  release targets, twice. That identity is a hard release-tag gate from v0.1.2
  on. The guarantee covers the builds we pin and test. It is not a mathematical
  property of the algorithm.
- **The x86_64 macOS target has a horizon.** That leg runs on `macos-15-intel`,
  GitHub's last Intel macOS runner image, which retires in autumn 2027.
- **A DRAT certificate proves one narrow thing.** `backend-instrument --certify`
  has CaDiCaL log a proof of an UNSAT verdict and has drat-trim check it against
  the exact CNF that was solved. That establishes that this CNF is unsatisfiable.
  Whether the CNF is the right encoding of the Alloy command is still the
  evaluator self-check's job for SAT answers, and the jar's for both.
- **`--conflicts` caps effort per solve,** and the solver stays usable
  afterwards. There is no decision-count budget.

## Solve budgets and capacity

- **`mettle exec` applies no solve budgets, on purpose.** The reference runs a
  command until it answers, and `exec` is the drop-in surface, so a wide `steps`
  range on a big model can genuinely grind (`leader.als` takes about 11 minutes).
  `--conflicts` and `--encode-budget` are the opt-ins. The conformance sweep owns
  budgeted runs.
- **A budgeted command that runs out reports a typed defer.** The verdict is
  never wrong, and every such command is solvable at a larger budget.

## Modules and the standard library

- **Only `util/*` is embedded** as the last-resort module fallback. The jar
  serves any of its bundled `models/*` files that way. A model that opens a
  non-util jar-embedded module fails to load in mettle. The alloy4fun run showed
  this is negligible: the only such cases were 6 codes whose jar rejection is a
  genuine parse error.
- **`util/ordering` exact pinning covers childless and enum ordered sigs only.**
  An ordered sig with children is governed by the hand-built `pred/totalOrder`
  formula instead. Verdicts and counts are jar-pinned either way. See
  [LEDGER-004](SEMANTICS_LEDGER.md).
- **Two `util/ordering` detection corners are unverified.** A module-level fact
  that spells the fields by explicit qualification (`Ord.First`) is deliberately
  not matched; the jar may pin there, and it has zero corpus incidence, so mettle
  under-approximates. The `pred/totalOrder` keyword over a genuinely non-exact
  element sig does not pin, and the jar's behaviour there was not probed.
- **`fun/add` index arithmetic could wrap.** In `util/sequence`'s `copy`,
  `append` and `subseq`, the index arithmetic can wrap at a `SeqIdx` scope past
  about 4 under bitwidth 4. Pre-existing and unprobed. Unverified.

## Internal differences that cannot change an answer

- The reference's reflexive `r = r` padding is not emitted. It keeps unreferenced
  relations alive for Kodkod's solver and carries no meaning.
- `Int/min` and `Int/max` relations are not bound. The jar bounds them and then
  never references them in its translation, because `fun/min` and `fun/max` lower
  as integer constants.
- The jar's redundant per-column membership constraints on arrow field bounds are
  omitted at every depth. They are entailed by the top-level membership.

## Permanent non-goals for v1

No native GUI (Sterling and the CLI only). No unbounded model checking (temporal
solving is bounded). No obscure syntax corners beyond those tracked here.

## How this file is maintained

Every construct that parses but cannot be solved is listed here and fails with a
precise message. mettle never answers wrongly. As each gap closes, its entry is
removed and the conformance scorecard in [docs/STATE.md](docs/STATE.md) records
the new agreement level.
