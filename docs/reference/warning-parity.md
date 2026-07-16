# Warning parity — the §5.2 catalog vs the reference jar (mt-023)

This is the evidence document for **bead mt-023**: mettle's implementation of the
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
| alloy4fun | 101,970 | **101,767 (99.80%)** | 192 (in 184 files) | 20 (in 18 files) | 14,180 | 14,001 | 13,981 (3,144) |
| corpus (167) | 167 | **166** | **0** | 1 | 9 | 10 | 9 (1) |

**mettle-missing = 0 on the corpus.** On alloy4fun the missing rate is
**0.19%** of agree-ACCEPT files (192 `(class,line)` misses / 14,180 jar warnings =
**98.6% recall**), each individually root-caused in §6.

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
167/167 corpus — unchanged throughout.**

## 6. Honest remainder (each root-caused)

### mettle-MISSING (LEDGER-002 direction)

- **`unused-var` (192, dominant).** A variable whose *only* occurrence is inside an
  **overloaded join that collapses to `none`** — the reference's ambiguous-
  `ExprChoice` → `none` rule (§4.4 case 6) replaces the sub-expression with `none`,
  eliminating the variable from the resolved tree its `hasVar` inspects, so the jar
  flags it unused. Example (`031193.als:74`): `all pr : Project | … p in pr.projects
  …` where `projects` is declared in two sigs → `Project.projects` collapses to
  `none` → `pr` eliminated → jar warns `pr` unused. mettle's syntactic `hasVar`
  counts the textual occurrence as a use. Matching this needs resolve-time
  survival tracking (materialize the resolved tree, or head-marking plumbing with
  cross-binder-scoping hazards); a proxy "empty-typed join eliminates its vars" was
  measured and **rejected** (it over-fired: +1,324 extra to save 17 misses).
  0.18% of files; the safe syntactic choice keeps **0 unused-var extra**.
- **`closure-redundant` (2), `join-empty` (3), `subset-redundant` (2).** Deep
  resolved-vs-bottom-up-type edges (e.g. `003056.als:42` `^(~(i.trans).^(i.trans))`
  nested in a comprehension; `005586.als:13` `adj in Node<:adj`, where the jar's
  `isSame` sees the full-domain `<:` as identity to `adj` — a semantic
  simplification mettle's structural `same_expr` does not perform).

### mettle-EXTRA (measured; the acceptable direction)

- **`eq-redundant` (18) + `subset-redundant` (2).** The `=`/`in` "same value" branch
  (`left.isSame(right)`, which the reference makes structural for `ExprBinary`).
  mettle's structural `same_expr` matches it — **except** the reference's `isSame`
  fails to fire on `+`/`-` compounds over a **var relation in a temporal formula**
  (`always ((A→B - f) + f) = (same)`, the train models `029361–029368`,
  `059866.als:99`), for temporal-resolution reasons mettle does not model at Rung 2
  (temporal is typed-but-not-solved). A guard that suppressed *all* var references
  was measured and **rejected** — it also suppressed the common `Protected =
  Protected` (var-sig) cases the jar *does* warn, trading ~12 new misses for ~9
  fewer extras (the wrong direction under LEDGER-002). Kept structural; the extras
  are one narrow, named pattern.
- **`plus-irrelevant` (1, corpus).** `util/seqrel.als:97` `s1 + shift.s2` inside a
  `let` with a comprehension bound — a mettle type-precision edge where the `+`
  relevant-slice intersection is empty for the comprehension operand only in
  mettle's approximation. One stdlib fun; not user-reachable divergence.

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

```sh
# jar side (one batch pass; chunk for memory safety on the 150k set)
javac -cp oracle/org.alloytools.alloy.dist.jar -d <out>/shim \
  crates/als-conform/shim/ResolveGaugeShim.java
java -cp <out>/shim:oracle/org.alloytools.alloy.dist.jar \
  ResolveGaugeShim <filelist.txt> > jar.jsonl

# mettle side (writes mettle.jsonl with warnings)
resolve-gauge alloy4fun --corpus corpus/alloy4fun/<set> --out <out>/a4f
resolve-gauge paths <corpus-paths.txt> --out <out>/corpus

# parity
resolve-gauge warn-diff --mettle <out>/a4f/mettle.jsonl --jar jar.jsonl
```

Regression tests (jar-pinned minimal model per class):
`crates/als-types/tests/warning_probes.rs`.
