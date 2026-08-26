# ADR-0029 — Translation classes: reproducing the jar's polarity-blind formula cache without reverting mt-056

**Status:** Accepted (tech lead, no-fork delegation, 2026-08-26) — the design pass for mt-137, the [ADR-0028](0028-zero-gap-campaign.md) campaign's last bead
**Date:** 2026-08-26

## Context

The jar memoises every translated formula in `FOL2BoolCache` keyed on **node
object identity plus a snapshot of the node's free-variable bindings — never
polarity** (`Environment.negated` is not consulted by the cache; the stored
value is returned verbatim, never re-guarded). So wherever one Kodkod formula
node is reachable twice from the goal, the second reach reuses the first
visit's translation wholesale, including its `noOverflow` guard direction. At
`for exactly 8 Node` (bitwidth 4, `#Node` overflows), `let p = (#Node < 0) |
p or (not p)` and `P or (not P)` over a zero-param pred are jar forbid-SAT
where polarity-correct translation gives UNSAT.

mettle translates each use at its own polarity because `lower.rs` mints fresh
IR per formula-`let` use (mt-056's deliberate lazy formula-`let` — freezing at
the binding site minted skolems the jar refuses) and per pred/fun call.
mettle's answer is the sounder one, but the North Star is drop-in.

Two research maps (jar contract; mettle pipeline) plus two probe waves
(`scratchpad/probe/mt128/` x5/x6, `scratchpad/probe/mt137/` — 16/16 banked
predictions hit) pinned the full mechanism; the behavioral rule is
[LEDGER-017](../../SEMANTICS_LEDGER.md). The load-bearing boundary facts:

1. Sharing is by node identity, never syntactic identity (two lets binding
   identical formulas do not share).
2. The only formula-level producers of shared nodes are a **`let` binding**
   (the env stores the translated object) and a **zero-parameter pred call**
   (`cacheForConstants` is keyed on the `Func` alone and bypassed whenever
   `f.count() > 0` — probe cells j2/j3: one parameter, even with the identical
   argument at both calls, severs sharing).
3. The reused value is the whole first-visit translation: int-comparison
   guards, `in`/`=`/multiplicity guards over `Int[..]`-derived operands (j4),
   and a whole quantified formula's translation (j5).
4. The jar's cache is built **post-skolemization**: an occurrence the
   skolemizer rewrites stops sharing (j6 — `p and (not p)` over an
   existential let stays UNSAT because only the positive occurrence
   skolemizes).
5. Zero-param **fun** sharing (Expression/Int level) is polarity-clean (j8);
   only formula-level caching is observable. Same-polarity reuse is
   observationally neutral (h4).
6. The jar's evaluator runs the identical `FOL2BoolTranslator`/`FOL2BoolCache`
   machinery over the instance, with a fresh Alloy-level translator (fresh
   `cacheForConstants`) per evaluated expression.

The mettle map's decisive finding: the encoder's existing caches are already
keyed `(node id, env-of-free-vars)` with **no polarity component**
(`encode/mod.rs` `formula_cache`/`int_cache`, `env_key()`), and the evaluator
is unmemoised and therefore polarity-correct by construction. The entire gap
is upstream: lowering never lets the polarity-blind cache see a shared node.

## Decision

**Keep per-use lowering exactly as it is (mt-056 untouched), and add
"translation classes": a side table grouping the use-copies that the jar
would have translated as one shared node, consulted first-visit-wins by both
the encoder and the evaluator.**

1. **Classes minted at lowering** (`lower.rs`). `LoweredGoal` carries
   `trans_classes: BTreeMap<FormulaId, TransClassId>` (typed id). One fresh
   `TransClassId` per:
   - **formula-valued `let` binding instance** — each `Binding::Formula`
     created in `push_let_bindings` gets a class; every use lowered through
     `lookup_binder_formula` registers its produced root `FormulaId` under it;
   - **zero-parameter pred, per command lowering** — one class per callee
     `Func` identity spanning the whole goal (the jar's `cacheForConstants`
     lives on the translator instance, so calls in facts and the command body
     share); every `inline_pred` with an empty parameter list registers its
     produced root `FormulaId`. Calls with any parameter mint no class (probe
     j2/j3). Zero-param funs mint no class (j8: polarity-clean).
2. **Class validation.** Before the table ships on the goal, every class with
   fewer than two members is dropped, and every class whose members are not
   **structurally identical** (a span-insensitive equality walk over the IR
   arena, skolem relation ids included in the comparison) is dropped. This is
   the mt-056 compatibility hinge: per-use lowering keeps making per-use
   skolem decisions, and wherever those decisions differ — or mint distinct
   skolem relations — the copies differ structurally and the class dissolves,
   which is exactly the jar's post-skolem severing (j6). Where no skolem
   fires, copies are identical by construction (uses re-lower under the
   binding-site binder stack), matching the jar's surviving shared node.
3. **Encoder reuse** (`encode/mod.rs`). A new
   `class_cache: BTreeMap<(TransClassId, EnvKey), Bool>` is consulted in
   `formula()` before encoding any classed node and populated after: the
   first visit (in the encoder's existing deterministic traversal order)
   encodes at its ambient polarity; every later visit — any polarity, same
   env — returns the stored value verbatim. Guard direction, quantifier
   orientation, everything from the first visit rides along, which is the
   jar's semantics by construction. The `EnvKey` half reuses `env_key()` over
   the node's free variables (all members of a valid class have the same free
   variables), reproducing the jar's per-tuple keying under quantifiers.
4. **Evaluator parity** (`eval.rs`). The evaluator gains the matching memo:
   `(TransClassId, env bindings) -> guarded truth`, populated at first visit,
   consulted at every later one. This keeps the post-solve self-check
   coherent — without it, every new jar-matching SAT verdict would trip the
   self-check, since an unmemoised evaluator is polarity-correct — and it
   matches the jar's evaluator, which shares the same machinery (a REPL query
   lowers fresh, so it gets fresh classes per query, exactly like the jar's
   fresh per-eval translator).
5. **Temporal is out of scope.** Classes are consulted on the static path
   only; temporal elimination re-mints per-state copies and the table does
   not follow them. The jar's temporal path presumably carries the same cache
   lineage, but the temporal × overflow × cross-polarity-sharing intersection
   is unprobed and has zero corpus incidence; LIMITATIONS records it.

## Alternatives considered

- **Revert to eager formula-`let` lowering** (translate once at the binding
  site, share the node): refuted at mt-056 — the binding site's polarity
  context made skolem decisions the jar refuses (44/44 parity only with
  per-use lowering). The jar itself skolemizes per occurrence on the shared
  node and only then caches, so binding-site freezing is not its semantics.
- **Share `FormulaId`s outright in lower.rs** (lower at first use, reuse the
  id): couples skolemization to encode-order first-use, and cannot express
  "copies diverged, sharing severed" (j6) without re-lowering anyway.
  Validation-by-structural-identity over per-use copies gets the same reuse
  with none of the coupling.
- **Structural hashing at encode time** (merge equal subtrees): wrong — the
  jar shares by node identity only; `(#Node<0) or (not (#Node<0))` written
  out twice is forbid-UNSAT (g5_dup_shared, h2_two_lets) and structural
  merging would flip it.

## Consequences and disclosed approximations

- The eight banked divergent cells (mt-128 g5_let_shared, h1, h3, h5; mt-137
  j1, j4, j5, j7) flip to jar parity; the ten agreeing boundary cells must
  not move. All land in a jar-free conformance test with the cells verbatim.
- **First-visit order** is mettle's deterministic encode order. It matches
  the jar's depth-first left-to-right traversal wherever conjunct order and
  constant folding coincide (all probe cells); the jar's short-circuit
  folding can in principle pick a different "first" on exotic shapes —
  undisclosed divergence risk accepted, zero incidence, recorded in
  LIMITATIONS.
- **Encoder/evaluator coherence** is an invariant, not an assertion: both
  walk the same IR with the same `Not`-only polarity flip and the same
  traversal order, so their first visits agree. Any violation surfaces as a
  self-check failure, which the sweep gates at zero.
- Same-polarity reuse through a class changes emitted circuit structure on
  models with repeated zero-param pred calls (fewer duplicate gates). Verdicts
  and model counts are unaffected (the boolean function is identical); the
  particular first instance a SAT command surfaces can shift, which the
  sweep's count nets and baselines will confirm as verdict/count-neutral.
- The stage-1 sweep runs immediately after implementation (encoder-touching
  change), plus both SB nets against cached baselines.

## Addendum at implementation (2026-08-26, tech lead) — decision 4 extended

The implementation surfaced one fact this ADR had not accounted for, and the
accepted fix extends decision 4. mettle's formula-`if`/`then`/`else`
desugaring lowers the condition **once** and negates that same `FormulaId`, so
the encoder's per-id `formula_cache` — polarity-blind since mt-049 — was
already reusing the positive visit's guard at the negated reach. That is
jar-faithful (the jar's `visit(ExprITE)` builds `c.implies(t) and
c.not().implies(e)` around ONE `c` node, which its cache then shares the same
way), but it meant the unmemoised, polarity-correct evaluator could reject an
instance the solver had just produced: probe cell `g5_let_shared_ite` tripped
the debug self-check with no translation class involved at all — a
pre-existing latent incoherence, not something this bead introduced.

So the evaluator gains **two** memos, not one: the class memo this ADR
specified, and a per-id memo that is the exact twin of the encoder's mt-049
`formula_cache`. Both are armed only when they can matter (the goal has
classes, or some formula node is referenced twice in the arena) and cleared
per instance. The per-id memo is also a measured speedup — the debug
`solve_corpus` gauntlet drops from 532s to 69s, because the evaluator was
re-walking shared DAG subtrees.

Two implementation details worth recording: a root registered under two
classes (a formula-`let` whose body is a bare use, inside a zero-param pred)
resolves deterministically to the outer pred class (minted first, lower id);
and the structural-identity walk compares bound variables up to a
correspondence (re-lowering a `let` RHS containing a quantifier allocates
fresh `VarId`s per copy while the jar still shares that node — probe j5), with
a 1M node-pair meter per class whose exhaustion drops the class, costing at
worst the parity it would have bought, never soundness. REPL fragments carry
no classes (`lower_fragment` has no goal to hang the table on; the jar's
evaluator gets a fresh translator per query anyway) — the one visible residue
is recorded in LIMITATIONS.
