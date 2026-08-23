# Warning parity — the §5.2 catalog vs the reference jar (mt-023, mt-118)

This is the evidence document for **bead mt-023** (closed to a single residual cell
by **mt-118**): mettle's implementation of the
full [alloy6-resolution.md](alloy6-resolution.md) **§5.2 warning catalog** and the
measured parity of its warning *sets* against the reference Alloy 6.2.0 jar. It
is the discharge of the **LEDGER-002 owner requirement**: *wherever the jar warns,
mettle warns — equivalent issue and position; wording may differ. Warnings never
flip the ACCEPT/REJECT verdict; `--strict` promotes them to a failing exit.*

Warnings are a **secondary** conformance target: the reference emits them only
*after* `resolveAll` fully succeeds and `A4Reporter.NOP` drops them, so they never
change the verdict (resolution-doc §0/§5.3). The one gauge that matters for the
scorecard — accept/reject — is **unchanged** by everything here (re-verified: 0
jar-accepts/mettle-rejects, 314 over-accepts, corpus 167/167, byte-identical
disagreement list).

## 1. Methodology

**mettle side.** Each `ResolveWarning` variant is typed, spanned, and render-free
(`crates/als-types/src/warning.rs`); the resolver emits it under the reference's
exact firing condition (source-verified at the pinned build commit `794226dd`),
ordered by source `Span` (§8). Each variant maps to a stable **class** string
(`ResolveWarning::class`).

**jar side.** `crates/als-conform/shim/ResolveGaugeShim.java` was extended
*additively* with a capturing `A4Reporter` (the `ProbeShim` precedent): every
ACCEPT record grows a `warnings: [{line, col, message}]` field. Every field the
mt-020/mt-024 readers already consumed (`file`, `ok`, `phase`, `nanos`) is
untouched, so those gauges still work. One batch JVM pass over a file list yields
the jar's warning set for every file.

**The gauge.** `resolve-gauge warn-diff --mettle <m.jsonl> --jar <j.jsonl>`
(`crates/als-conform/src/bin/resolve_gauge.rs`) joins the two streams by file and,
**on agree-ACCEPT files only**, compares warning *sets*. The jar's message stems
are mapped to the same class vocabulary by `als_types::jar_stem_class` (the stem
table below). Each file is classified exact-match / mettle-missing / mettle-extra.

**Position matching is at line granularity.** The reference attaches an
operator warning (`&`, `.`, `<:`, …) to the operator glyph's `Pos`; mettle's
surface AST carries one `Span` per node (no separate operator span — adding one
would touch `als-syntax`, out of scope), so a binary-operator warning lands at the
node's start (the left operand) — same *line*, shifted *column*. §8 already
declares the jar's warning **order** JVM-incidental and pins the gauge to compare
sets, not order; for the same reason the column difference is incidental and the
gauge matches on `(class, line)`, reporting column-exact agreement as a secondary
metric. Prefix-unary and sub-expression warnings (closure `^`, `int[]`/`sum`,
unused binder, ITE branch, function-return-disjoint) *do* land column-exact.

## 2. Stem → class table

The jar-message-stem → class map (`jar_stem_class`), derived from the exact §5.2
message strings. Order matters where one stem prefixes another.

| jar message stem (first line) | class |
|---|---|
| `This variable is unused.` | `unused-var` |
| `… is redundant since its domain and range are disjoint` | `closure-redundant` |
| `The value of this expression does not contribute to the value of the parent` | `not-contribute` |
| `This expression should contain Int atoms` | `int-atoms` |
| `== is redundant, …` | `eq-redundant` |
| `Subset operator is redundant, …` | `subset-redundant` |
| `& is irrelevant …` | `intersect-irrelevant` |
| `The join operation here always yields an empty set` | `join-empty` |
| `<: is irrelevant …` | `domain-irrelevant` |
| `:> is irrelevant …` | `range-irrelevant` |
| `- is irrelevant …` | `minus-irrelevant` |
| `+ is irrelevant …` / `++ is irrelevant …` | `plus-irrelevant` |
| `The left/right expression of -> is irrelevant …` | `arrow-irrelevant` |
| `This subexpression is redundant.` | `redundant-ite-branch` |
| `Implicit in-line conjunction between two formulas` | `implicit-conjunction` |
| `Part of … is static.` | `sig-static-var-parent` |
| `Marking sig … as var is redundant` | `sig-redundant-var` |
| `Static field types with variable bound` | `field-static-var-bound` |
| `Static field inside variable sig` | `field-static-in-var-sig` |
| `Function return value is disjoint from its return type` | `return-disjoint` |

The gauge reports any jar stem it **cannot** classify (expected: none) — a tripwire
that the stem table has drifted from the jar.

## 3. Catalog coverage (every §5.2 stem)

Every branch of the §5.2 catalog is implemented in the mt-025 top-down pass
(`crates/als-types/src/resolve/expr.rs`), plus the sig/field passes (`sigs.rs`,
`members.rs`). Firing conditions are ported from the reference (`ExprUnary`/
`ExprBinary`/`ExprITE`/`ExprQt`/`ExprLet`/`ExprList.resolve`, `CompModule.resolveSig`/
`resolveFieldDecl`/`resolveFuncBody`); all use the node's **bottom-up** (`.type`)
types the reference's conditions read.

| § | class | reference site | condition | status |
|---|---|---|---|---|
| A1 | `closure-redundant` | `ExprUnary` `^` | `type.join(type).hasNoTuple()` (`^` only) | ✅ |
| A2 | `not-contribute` | `ExprUnary` `~`/`^`/`*` | `resolveClosure(p, sub.type)==EMPTY && p.hasTuple()` (ported `resolveClosure`) | ✅ |
| A5 | `int-atoms` | `ExprUnary` CAST2INT (`int[]`/`sum`) | `sub.type ∩ Int == ∅` | ✅ |
| A3 | `eq-redundant` | `ExprBinary` `=`/`!=` | disjoint types, or `left.isSame(right)` | ✅ |
| A4 | `subset-redundant` | `ExprBinary` `in`/`!in` | side empty, disjoint, or `isSame` | ✅ |
| A6 | `intersect-irrelevant` | `ExprBinary` `&` | `type.hasNoTuple()` | ✅ |
| A7 | `plus-irrelevant` | `ExprBinary` `+`/`++` | `left∩p==∅` or `right∩p==∅` | ✅ |
| A8 | `minus-irrelevant` | `ExprBinary` `-` | `type.hasNoTuple() || (p∩right).hasNoTuple()` | ✅ |
| A9 | `join-empty` | `ExprBinary` `.` | `type.hasNoTuple()` (legal arity) | ✅ |
| A10 | `domain-irrelevant` | `ExprBinary` `<:` | `type.hasNoTuple()` | ✅ |
| A11 | `range-irrelevant` | `ExprBinary` `:>` | `type.hasNoTuple()` | ✅ |
| A12 | `arrow-irrelevant` | `ExprBinary` default (17 arrows) | one side `hasTuple`, other `hasNoTuple` | ✅ |
| B | `unused-var` | `ExprQt`/`ExprLet` | `!hasVar(x)` and no later decl-bound uses it (comprehensions exempt) | ✅ |
| C | `redundant-ite-branch` | `ExprITE` | `branch.type.hasTuple() && (branch.type∩p).hasNoTuple()` (`p.size>0`) | ✅ |
| D | `implicit-conjunction` | `ExprList.makeAND` | two juxtaposed formulas on one source line, no explicit `and` | ✅ |
| E(a/b) | `sig-static-var-parent` | `resolveSig` | static sig, variable parent (subset + prim) | ✅ |
| E(c) | `sig-redundant-var` | `resolveSig` | variable sig, static parent (**prim `extends` only**) | ✅ |
| E(d) | `field-static-var-bound` | `resolveFieldDecl` | static field, bound references a var sig | ✅ |
| E(e) | `field-static-in-var-sig` | `resolveFieldDecl` | static field inside a variable sig | ✅ |
| F | `return-disjoint` | `resolveFuncBody` | `ret.hasTuple() && body.hasTuple() && !body∩ret` | ✅ |

No stem is deferred. The dead-code entries the reference never emits from
well-formed input (`Sig.java` "Undefined case", commented-out `ExprCall`/
`resolveFuncBody` experimental branches) are correctly *not* implemented.

## 4. Measured parity

Gauge run over the **150,891-code alloy4fun** differential (101,970 agree-ACCEPT
files) and the **167-file corpus** (all agree-ACCEPT). Match key `(class, line)`.

| corpus | agree-ACCEPT files | identical warn set | mettle-MISSING | mettle-EXTRA | jar warnings | mettle warnings | matched (col-exact) |
|---|---|---|---|---|---|---|---|
| alloy4fun | 101,970 | **101,969 (99.999%)** | 1 | 1 | 14,180 | 14,180 | 14,179 (3,370) |
| corpus (167) | 167 | **166** | **0** | 1 | 9 | 10 | 9 (1) |

**Campaign arc.** mt-023 first measured full-catalog parity at 101,767/101,970
identical (99.80%), missing 192 `(class,line)` cells and extra 20. Every resolve-
level campaign from mt-105 through mt-117 explicitly measured **zero warning
changes** across all 150,891 codes while reshaping the agree-ACCEPT population
underneath — so parity held flat, and the count drifted only through that
population shift: mt-118 started from 101,772/101,970 identical, missing 194
(192 `unused-var` + 2 `subset-redundant`), extra 20 (18 `eq-redundant` + 2
`subset-redundant`). mt-118 (§5 items 7–10) closed all of it but one
line-attribution artifact, landing at **101,969/101,970 (99.999%)**, missing 1,
extra 1 — the jar's and mettle's total `(class,line)` warning counts are now
**exactly equal** (14,180 = 14,180). The one remaining cell pair is root-caused
in §6.

## 5. Fixes and iterations

The catalog started partial (unused-binder + one var/static case). Building it to
parity took these measured iterations:

1. **Full catalog implemented** from the source-verified conditions (recon of the
   `warns`-emitting branches). Initial gauge: 0 corpus missing, but large
   **mettle-EXTRA** in two classes.
2. **unused-var over-warning (6,814 alloy4fun + 261 corpus extra)** — the old
   `used`-set tracked variable uses as a *resolve-time side effect*, missing a
   variable used only as a **join spine head** (`proc.p`, `p.parent`). Replaced
   with the reference's **syntactic `hasVar`** (`references_name`, shadowing-aware)
   over the body and later decl bounds. → 0 extra.
3. **sig-redundant-var over-warning (863 + 2)** — the reference emits the redundant-
   `var` warning only in the prim-`extends` branch; a subset (`var sig A in B`) with
   a static `B` never warns. Restricted to prim. → 0 extra.
4. **closure-redundant / join-empty / domain / range missing (125+25+…)** — these
   live inside **compound right operands of joins** (`b.head.^key.hash`), which
   mettle deliberately does not resolve for the *verdict* (the documented
   LIMITATIONS over-acceptance). Added a **warning-only** resolve of the compound
   right operand that **discards errors** (`Fin::Join` carries the operand
   `ExprId`), keeping the verdict byte-identical. → closure 125→2, join-empty 25→0.
5. **not-contribute missing (38)** — the A2 condition needs the reference's
   `resolveClosure` graph-reachability, not a proxy. **Ported `resolveClosure`
   faithfully** (used for the warning decision only, so the pushed relevant type —
   and the verdict — is unchanged). → 0.
6. **int-atoms missing (5)** — the CAST2INT warning also fires for the `sum` prefix
   (`sum e`), not just `int[e]`. Extended A5 to `SumOf` and the box-join `sum`
   path. → 0.

Each iteration re-ran the verdict diff: **314 over-accepts, 0 drop-in violations,
167/167 corpus — unchanged throughout.** Iterations 7–10 below (**mt-118**,
2026-08-24) closed the entire remainder that iterations 1–6 left standing,
pinned against the reference source at commit `794226dd` and validated cell-
for-cell against the banked jar baseline (`crates/als-types/tests/warning_probes.rs`).

7. **unused-var, overload-collapse-to-`none` (missing 192 → 0)** — an ambiguous
   overloaded join (`x.field` where `field` is declared on ≥2 sigs, all
   type-disjoint from `x`'s domain) is silently folded to the `none` constant by
   the reference's `ExprChoice.resolveHelper` *before* `ExprQt.resolve()`/
   `ExprLet.resolve()` ever walk the body — erasing the binder from the tree the
   reference's `hasVar` inspects, so the jar flags it unused even though the
   textual occurrence is right there. mettle's rule-6 empty-spine accept is the
   analog of that fold: `record_spine` now notes the folded `ExprId`s in a `fold`
   set on `Cx` (trial-gated like the choice table below — marking only, pick
   outcomes untouched), and `references_name` treats a folded subtree as
   containing no references. This retires the mt-023 "resolve-time survival
   tracking needed" note and the rejected over-firing proxy — the fold set is the
   cheap, precisely-targeted mechanism that proxy was missing.
8. **unused-var, duplicate binders (bundled into the same 192 → 0)** — a
   quantifier that binds one source name twice (`all x : A, x : B | …`) shadows
   by reference identity in the reference: every body occurrence of the name
   binds to the *last* `Decl`'s `ExprVar` object, so the *first* declared binder
   is the one flagged unused, never the second. The unused-var check now
   replicates that shadow interval exactly (body and later-decl-bound references
   resolve to the last matching binder) instead of crediting a textual
   occurrence to every binder of the name.
9. **eq-redundant + subset-redundant, choice-identity non-firing (extra 18 eq +
   1 of 2 subset → 0)** — the reference's redundancy check (`left.isSame(right)`
   in `ExprBinary`'s
   `=`/`!=`/`in`/`!in` arms) runs on the pre-disambiguation operands, and
   `ExprChoice` never overrides `isSame` — it falls to `Expr`'s default, pure
   Java object identity. Every textual occurrence of an overloaded name or join
   gets its own distinct `ExprChoice` object from `CompModule.process()`, so two
   occurrences of the same overloaded field never compare same even when both
   resolve to the identical candidate — the redundancy warning silently doesn't
   fire. mettle's structural `same_expr` doesn't share that blind spot by
   default, so it was firing where the jar wasn't: nodes whose raw candidate
   count exceeded one at collection time are now noted in a `choice_wrapped` set
   on `Cx` (trial-gated marking, mirroring the `fold` set), and `same_expr`
   reports not-same whenever either side is marked. This closes all 18
   eq-redundant extras (the `Component`/`Robot`/`Photo`/`Album` field-overload
   family plus the `029361–029370` train-model family) and one of the two
   subset-redundant extras (`062913.als:55`, `Person.projects`/`Course.projects`
   overloaded) — the other subset-redundant extra, `059866.als:99`, is unrelated
   to choice identity; it's the line-attribution artifact in §6. Discovery along
   the way: `util/integer` is auto-opened into every module and exports
   `pos`/`neg`/`zero`/`min`/`max`/… as funs/preds, so a field literally named
   `pos` (or `neg`, `zero`, …) is invisibly overloaded even when declared
   exactly once — this is what the train-model cells actually were, not the
   "var relation in a temporal formula" mt-023 originally characterized them as
   (refuted; see §6).
10. **subset-redundant, `Sig<:field` domain-collapse identity (missing 1 → 0)** —
    `005586.als:13`, `adj in Node<:adj`. The reference's `ExprBinary.Op.make`
    DOMAIN case returns the right operand outright when it is a `Field` whose
    declaring sig is exactly the left operand, so a no-op restriction like
    `Node<:adj` never exists as a distinct node — `adj in Node<:adj` is, by
    identity, `adj in adj`, and the subset-redundant warning fires by the same
    `isSame` reference-identity path as item 9. mettle keeps the surface
    `Node<:adj` node (no construction-time collapse) and instead teaches
    `same_expr` to dereference such restrictions before comparing — owner-
    identity only, unwrapped operands only, recursive for chains.

## 6. Honest remainder (each root-caused)

**mt-118 (2026-08-24) closed the whole EXTRA family and all but one cell of the
MISSING family** (§5 items 7–10). What's left is a single cell pair, plus one
unrelated corpus item mt-118 never touched.

### The residual: `059866.als:99`/`100` — a line-attribution artifact, not a semantic miss

The formula spans two source lines:

```
99:  all s : Student, c : s.enrolled | ( s.(c.grades)
100: in max[c.grades]) implies some(s.projects & c.projects)
```

The reference's CUP grammar constructs the `IN` `ExprBinary` with `pos` bound to
the **`in` token's own position** (`Alloy.cup:985`, `CompareExprA ::= ... IN:o
...`), not the left operand's span-start, so the jar's subset-redundant warning is
anchored to line 100 (the operator glyph) — confirmed against `jar.jsonl`.
mettle's surface AST carries **one `Span` per node** with no separate
operator-glyph position (already flagged as out of scope for the `als-syntax`
shape in §1 above), so the binary-operator warning is emitted at the node's
overall span start — line 99, the left operand. The gauge's `(class, line)` match
key can't merge these back together: it shows as a MISSING at
`(subset-redundant, 100)` and an EXTRA at `(subset-redundant, 99)` for what is,
underneath, the same logical warning firing in the same place for the same
reason. **Future fix:** thread an operator-glyph `Pos` distinct from the node's
full `Span` from the parser through to warning emission. Deferred as
disproportionate for one cell in 150,891 — the change touches `als-syntax`'s AST
shape for every binary node, not just this warning path.

### Superseded root-causes (mt-023-era characterizations, struck by mt-118)

- ~~**`unused-var` (192, dominant)… resolve-time survival tracking needed
  (materialize the resolved tree, or head-marking plumbing with cross-binder-
  scoping hazards); a proxy "empty-typed join eliminates its vars" was measured
  and rejected (it over-fired: +1,324 extra to save 17 misses).**~~ The pinned
  mechanism (§5 items 7–8: a `fold` set marking overload-collapsed spines plus
  duplicate-binder shadow-interval tracking) landed **without** needing that
  proxy or a materialized resolved tree — the fold set targets exactly the
  reference's silent `ExprChoice` → `none` collapse and nothing else, which is
  what the rejected proxy was missing.
- ~~**`eq-redundant` (18) + `subset-redundant` (2)… the reference's `isSame` fails
  to fire on `+`/`-` compounds over a var relation in a temporal formula**~~
  **REFUTED**, for the train-model half of the family (`029361–029370`, 9
  files — the other 9 eq-redundant files, `Component`/`Robot`/`Photo`/`Album`,
  were never characterized as temporal/var at all; they were always correctly
  understood as an overloaded-field `isSame` gap). The train-model cells don't
  turn on `var`-ness or the temporal operator either — they turn on the field
  being named `pos`, which collides with `util/integer`'s auto-opened funs/preds
  of the same name and is therefore invisibly overloaded (§5 item 9), exactly
  the same mechanism as the non-temporal half of the family. `var`-ness and the
  temporal wrapper were coincidental to the train models, not causal.
  Probe-verified: `scratchpad/mt118/probe3b/` isolated the suppression to the
  literal name `pos` (24 probes, 91/91 corpus cells, clean controls) before
  proposing a name carve-out; `scratchpad/mt118/tlprobe/` then refuted that
  carve-out by showing fields named `neg`/`zero` suppress identically while `f`
  warns normally — the real mechanism is the namespace collision, not the
  string `"pos"`.
- ~~**`closure-redundant` (2), `join-empty` (3), `subset-redundant` (2 — the
  `005586.als:13` `Node<:adj` case)**~~ The closure/join-empty pair closed
  silently at **mt-105** (the compound-right-operand resolve fixes, ADR-0023);
  `005586.als:13` closed at **mt-118** (§5 item 10, the DOMAIN construction-
  collapse deref). Neither is part of the remainder above.

### mettle-EXTRA, untouched by mt-118 (one corpus item, unrelated mechanism)

- **`plus-irrelevant` (1, corpus).** `util/seqrel.als:97` `s1 + shift.s2` inside a
  `let` with a comprehension bound — a mettle type-precision edge where the `+`
  relevant-slice intersection is empty for the comprehension operand only in
  mettle's approximation. One stdlib fun; not user-reachable divergence; not part
  of the mt-118 campaign (a different mechanism from the choice-identity family).

## 7. `mettle check --strict`

`mettle check <file>` renders every warning to stderr (`warning:`-labeled caret
block, `crates/mettle/src/diagnostics.rs`) and prints an ACCEPT summary; the exit
code is **0** regardless of warnings (the reference verdict). `--strict` promotes
any warning to **exit 1** with a summary line that says why
(`… : FAILED (strict): N warning(s) …`) — the verdict itself is unchanged
(LEDGER-002); warnings still render. CLI tests: `crates/mettle/tests/check.rs`
(`strict_fails_when_a_warning_fires`, `strict_passes_a_clean_model`,
`warnings_without_strict_still_exit_zero`).

## 8. Reproducing

**Default: JVM-free, from the committed jar baseline (mt-118).** The reference's
per-file warning sets over all 150,891 alloy4fun codes are baked into
`baselines/alloy4fun-warnings.txt` (one line per jar-accepted code with ≥1
warning, keyed by code id, warnings as sorted `class@line:col` triples under a
jar-sha-pinned header) — the same "immutable fact, stop re-deriving it" move
mt-110 made for verdicts. `warn-diff --jar-baseline` reconstructs the jar side
from this file plus the existing resolve-verdict baseline instead of running a
live JVM pass; it shares one report body with the live-jar path, so the two
cannot drift, and a full parity run drops from a multi-minute chunked JVM sweep
to seconds:

```sh
# mettle side (writes mettle.jsonl with warnings)
resolve-gauge alloy4fun --corpus corpus/alloy4fun/<set> --out <out>/a4f

# parity, JVM-free
resolve-gauge warn-diff --mettle <out>/a4f/mettle.jsonl \
  --jar-baseline baselines/alloy4fun-warnings.txt
```

**Re-baking the baseline** (only needed after a jar upgrade or a corpus change):

```sh
# jar side (one batch pass; chunk for memory safety on the 150k set)
javac -cp oracle/org.alloytools.alloy.dist.jar -d <out>/shim \
  crates/als-conform/shim/ResolveGaugeShim.java
java -cp <out>/shim:oracle/org.alloytools.alloy.dist.jar \
  ResolveGaugeShim <filelist.txt> > jar.jsonl

resolve-gauge bake-warnings --jar jar.jsonl --out baselines/alloy4fun-warnings.txt

# corpus (167) and any one-off comparison still take the live-jar path
resolve-gauge paths <corpus-paths.txt> --out <out>/corpus
resolve-gauge warn-diff --mettle <out>/a4f/mettle.jsonl --jar jar.jsonl
```

Regression tests (jar-pinned minimal model per class):
`crates/als-types/tests/warning_probes.rs`.
