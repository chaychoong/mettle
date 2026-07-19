# Alloy 6 translation & solving — pinned contract for mettle

This document pins **exactly how the reference implementation turns a resolved,
type-checked model into a bounded relational problem, hands it to SAT, and reads
the answer back** — the phase that runs *after* resolution (mt-016..026,
[alloy6-resolution.md](alloy6-resolution.md)) and produces the verdict a user
sees from `run`/`check`. It is the **fixed contract for Rung 3** (ROADMAP rung 3:
"it actually solves my models" — `mettle run`/`check` returns a correct instance
or "no counterexample", self-verified): implement *this*, not memory and not the
public language docs.

Provenance — all Java read at the jar's build commit
`794226dd07b536fe35c5ca44b529417183cd629b` (the pinned oracle build, ADR-0002).
The Alloy→relational→CNF pipeline spans two source trees in the same repo, both
in scope for behavior-pinning:

- `org.alloytools.alloy.core/.../translator/`:
  - `ScopeComputer.java` — command scopes → per-sig scope → the atom universe.
  - `BoundsComputer.java` — sigs/fields → relations with lower/upper tuple bounds.
  - `TranslateAlloyToKodkod.java` — resolved `Expr` → Kodkod relational AST;
    facts/command formula assembly; skolem naming; `pred/totalOrder` detection.
  - `A4Solution.java` — the solve object: builds the Int/String/seq bounds, wires
    the Kodkod (Pardinus) solver options, runs the solve, decodes SAT/UNSAT,
    enumerates, and evaluates expressions against a found instance.
  - `A4Options.java` — the translator's tunables (`symmetry`, `noOverflow`,
    `solver`, `skolemDepth`, …) and their defaults.
  - `Simplifier.java` — the default partial-instance bound-tightening pass.
  - `A4Tuple.java` / `A4TupleSet.java` — the decoded instance's tuple view.
- `org.alloytools.pardinus.core/.../kodkod/` — the relational engine Alloy drives
  (a temporal fork of Kodkod, package `kodkod.*`). Behaviorally in scope:
  `engine/config/Options.java` (bitwidth, symmetry, int encoding, overflow),
  `engine/fol2sat/{SymmetryBreaker,SymmetryDetector}.java` (symmetry breaking),
  `instance/{Bounds,TupleSet,Universe}.java`, `ast/…totalOrder` (the total-order
  relation predicate).

Per PORTING_RULES (legal hygiene, ADR-0006): these files were **read to pin
behavior**; mettle is written fresh from this document, never by transcribing
Java text or class structure. Every claim a reasonable implementer could get
wrong is either cited to a specific source method/behavior or marked
**jar-verified 2026-07-16** with the probe id from §10.

The scope of Rung 3's *vertical slice* vs. what defers to later rungs is set by
[ADR-0011](../adr/0011-rung3-translation-solving-architecture.md); this document
pins the *whole* contract so later rungs implement against one pinned reference.

---

## 0. The pipeline and what "solve" is measured against

`TranslateAlloyToKodkod.execute_command(rep, sigs, cmd, opt)` is the entry point
(the API the mt-006 harness already drives). For one command it runs, in order:

1. **`ScopeComputer.compute`** (§1): turn the command's scopes into a concrete
   integer scope for every sig, a bitwidth, a maxseq, a maxstring, a trace
   length, and — crucially — the **ordered list of atom names** (the universe).
   It constructs the `A4Solution` (which builds the fixed Int/seq/String bounds).
   May **throw** (→ a translation-time error, not SAT/UNSAT) on an illegal scope.
2. **`BoundsComputer.compute`** (§1.4): assign each sig and field a Kodkod
   *relation* with a lower/upper `TupleSet` bound, add sig-hierarchy /
   multiplicity / size constraint formulas, and pre-bind `util/ordering`'s
   first/next fields to exact constants where detected (§5).
3. **`TranslateAlloyToKodkod`** proper (§2): translate every fact, the command's
   formula (the pred body for `run`, the negated assert for `check`), and the
   sig/field constraint formulas into one big Kodkod `Formula`.
4. **`A4Solution.solve`** (§4): run the default `Simplifier` (partial-instance
   bound tightening), conjoin all formulas, hand the problem to the SAT backend
   (SAT4J by default) via the incremental `solveAll` enumerator, and decode the
   first `Solution` into SAT (a Kodkod `Instance`) or UNSAT (`null`).

**What the Rung-3 gauge measures** (ADR-0002): the **verdict** (SAT/UNSAT) — the
only solver-independent, canonical answer — and, secondarily, the **model count**
*only when symmetry breaking is identical on both sides* (the counting net runs
both mettle and the jar at `symmetry = 0`). **Instance tuples are never diffed
against the jar** (they depend on symmetry-breaking predicates, variable ordering,
and the solver); instance *validity* is checked by mettle's own evaluator (§6).

The overall **verdict** for a command is:
- **SAT** for a `run` command with a witnessing instance, or a `check` command
  whose negated assertion is satisfiable (→ a **counterexample** exists).
- **UNSAT** for a `run` with no instance, or a `check` whose negated assertion is
  unsatisfiable (→ **"no counterexample"**, the assertion holds within scope).

mettle presents these as: `run` SAT = "instance found"; `run` UNSAT = "no
instance"; `check` SAT = "counterexample found"; `check` UNSAT = "no
counterexample found (assertion holds up to this scope)".

---

## 1. Scopes → universe → bounds

### 1.1 Defaults (`A4Options` + `ScopeComputer`)

| Quantity | Default | Source |
|---|---|---|
| Overall scope (top-level sigs) | **3** (when the command gives no overall and no per-sig scope) | `derive_overall_scope`: `overall = (cmd.overall<0 && cmd.scope.size()==0) ? 3 : cmd.overall` |
| Bitwidth | **4** (Int atoms `-8..7`) | `setBitwidth`, `cmd.bitwidth<0 ? 4 : cmd.bitwidth` |
| `maxseq` (seq length / `seq/Int` size) | **4**, but capped: if unset, `= cmd.overall` when overall≥0 else 4, then clamped to `max(bitwidth)=7` | `ScopeComputer` ctor |
| `maxstring` | **−1** (only the String constants referenced by the command; no extra atoms) | field `maxstring` |
| `maxtrace` / `mintrace` | 10 / 1 (temporal only; −1 for static models) | `setMaxTraceLength`/`setMinTraceLength` |
| Symmetry breaking | **20** | `A4Options.symmetry` |
| `noOverflow` | **false** (allow/wraparound) — mettle's canonical default flips this to **true** per LEDGER-001 | `A4Options.noOverflow` |
| Skolem depth | 0 (skolem **constants** only, no skolem functions) | `A4Options.skolemDepth` |
| Solver | `SATFactory.DEFAULT` = SAT4J (pure Java) | `A4Options.solver` |

**`run` vs `check` have identical default scopes.** `ScopeComputer` never
branches on the command kind — both take the same `overall`/`bitwidth`/`maxseq`
path, so a bare `check` scopes exactly like a bare `run` (default overall 3).
(jar-verified: probe T1 — bare `run {}`/`run { some A }`/`check {…}` all resolve
at overall 3.)

### 1.2 Per-sig scope derivation (the exact rules)

`ScopeComputer` seeds scopes from the command's explicit `for … but N SIG`
clauses (validating each: no scope on `univ`/`Int`/`seq/Int`/`none`/an enum; a
`String` scope must be exact; a non-var `one` sig must be scope 1; non-var `lone`
≤ 1; `some` ≥ 1), forces every non-var `one` sig to **exactly 1** and non-var
`lone` sig to ≤ 1, then runs a **fixpoint** of three derivation rules in this
priority order (each re-run to exhaustion before falling through to the next):

1. **`derive_abstract_scope`** — for an `abstract` sig: if it is *unscoped* and
   **all** children are scoped, its scope becomes the **sum** of the children; if
   it is *scoped* and **all but one** child is scoped, the missing child's scope
   becomes the **difference** (clamped at 0). (An abstract sig with children never
   gets its own atoms — see 1.3.)
2. **`derive_overall_scope`** — any still-unscoped **top-level** sig gets the
   overall scope (default 3). An unscoped `enum` sig with no children gets 0. If
   overall is unspecified *and* per-sig scopes were given (the `for N1 SIG1…`
   with no leading `for N` form), an unresolved top-level sig is an **error**
   ("You must specify a scope for sig …").
3. **`derive_scope_from_parent`** — any still-unscoped **non-top-level** sig
   inherits its parent's scope; if the parent is itself unscoped it is an error.

Note this means, e.g., `abstract sig A {}` with children `B`, `C` and `for 4`:
the fixpoint sets `A=4` (overall), then `B=4` and `C=4` (from parent) — **each
child ≤ 4 independently; the `for 4` does NOT cap their sum.** (jar-verified:
probe T5.)

**Scope raise during the atom walk (mt-030 review, jar-verified 2026-07-16,
probe B19).** *After* the fixpoint, `computeLowerBound` silently **raises** any
sig's scope to the sum of its children's lower bounds when the children exceed
it (`if (n < lower) n = lower`, exactness preserved; a reporter message, never
an error). So `sig P {} sig C extends P {} run {} for exactly 2 P, exactly 3 C`
is **accepted**: `P` becomes exactly 3, the universe is `C$0 C$1 C$2` (no `P`
atoms), no size formula is emitted for `P` (its upper equals its raised scope),
and the command solves **SAT** — the `exactly 2 P` is effectively overridden,
not contradicted. The inexact form (`for 2 P, exactly 3 C`) raises `≤2` to `≤3`
identically.

### 1.3 The universe: atom names and order

`ScopeComputer.computeLowerBound` walks each top-level sig **recursively**
(children first) and appends atom names to `atoms`. An atom is created for a sig
only when `n > (sum of children's lower bounds)` **and** the sig is either
**exact** or **top-level** — i.e. an inexact non-top-level (child) sig draws its
atoms from the parent's pool rather than minting its own.

**Atom naming (pin exactly):**
- Sig atoms are `"<Name>$<index>"` where `<Name>` is the sig's label with the
  leading `this/` stripped (`Util.tailThis`) and made unique across sigs by a
  `UniqueNameGenerator`, and `<index>` is `0, 1, 2, …` — **plain decimal, no
  zero-padding** (a stale source comment claims zero-padding; the code appends the
  raw `int`). So a sig `A` scoped 3 yields `A$0 A$1 A$2`. (jar-verified: probes
  T1, T2 — `A$0..A$3` for `exactly 4 A`.)
- **Integer atoms** are the decimal strings `"-8" … "7"` (for bitwidth 4, i.e.
  `min(bw) … max(bw)`), appended **after all sig atoms**, in **ascending numeric
  order**. (jar-verified: probe T8 — `univ={A$0, -8, -7, …, 7}`.)
- **String atoms** (the referenced string constants, plus synthetic `"String0"…`
  to fill an exact `maxstring`) are appended **last**.

This ordered `atoms` list *is* the Kodkod `Universe`; **atom order is fixed here
and is the canonical order everything downstream numbers from** (STYLE D2). It
maps directly onto mettle's `als_core::bounds::Universe` (built once, in this
order). The pending Ledger "iteration-order-sensitive numbering" corner is pinned
by this rule: sigs in declaration order → their atoms in index order → ints
ascending → strings.

### 1.4 Bounds (`BoundsComputer`)

Each sig/field becomes a Kodkod **relation** with a lower bound (tuples it *must*
contain) and an upper bound (tuples it *may* contain). Bounds are built from the
universe atoms (consumed **from the end** of the ordered atom list, so lower atom
indices go to earlier-declared sigs):

- **Lower bound, bottom-up** (`computeLowerBound`): a sig's lower is the union of
  its children's lowers; if the sig is **exact** or **top-level** it consumes
  fresh atoms up to its scope — added to **both** lower and upper if exact, to
  the **upper only** if inexact-but-top-level.
- **Upper bound, top-down** (`computeUpperBound`): a parent's "floating" atoms
  (its upper minus every child's lower) are added to the upper of each child that
  can still grow — so children of a common parent share the parent's spare atoms.
- **Relation allocation** (`allocatePrimSig`, bottom-up):
  - a **leaf** sig → one fresh relation bounded `[lower, upper]`;
  - a **non-abstract** sig with children → the union of the children plus a fresh
    `"<Sig>_remainder"` relation (atoms in the parent but in no child);
  - an **abstract** sig with children → just the union of the children (**no own
    relation**);
  - **sibling disjointness**: `no (child_i & child_j)` (static) or a temporal
    variant (`[electrum]`, for `var` sigs) is asserted.
- **Subset sigs** (`allocateSubsetSig`, top-down): bounded by the union of their
  parents' uppers; an **exact** (`=`) subset sig *is* that union (no fresh
  relation); otherwise a fresh relation `r` with `r in (union of parents)`
  asserted.
- **Fields** (`s.label + "." + f.label`): a relation whose upper bound is the
  product of the per-column sig uppers (from the field type's `fold()`); a **`one`
  sig's** field prepends the singleton sig column (so the stored relation is the
  field value, then re-multiplied by the sig). A `one`-sig **defined** field
  (`f = e`) whose RHS is a simple relation combination is bound directly to that
  value. The **total-order-on-enum / `util/ordering`** special case is detected
  here and pre-bound to exact constants — see §5.
- **Size & multiplicity constraints**: for each sig with scope `n`, add
  `size(sig, n, exact?)` (an `exact` scope forces `#sig = n`; an inexact scope
  forces `#sig ≤ n`, expressed as a quantified formula), plus `one`/`some`/`lone`
  multiplicity formulas where the bounds don't already guarantee them. When
  lower==upper==n and the scope is exact, the bound alone suffices (no formula).

This maps onto `als_core::bounds::{Bounds, RelBound, TupleSet}` directly: one
`RelBound` per `RelId`, `RelBound::exact` for the pinned/exact cases, lower⊆upper
enforced (already asserted in the skeleton).

#### 1.4′ mt-030 pinned facts (jar-verified 2026-07-16, probes B1–B18)

The `BoundsShim`/`DumpK2` probes (§10.2) dumped `A4Solution.getBounds()` and
`debugExtractKInput()` at `symmetry=0`, `noOverflow=false`,
`inferPartialInstance=false` (the raw `BoundsComputer` output, before the
`Simplifier`). These sharpen §1.4 where it was compressed:

- **Child-growth condition (jar-verified).** A child absorbs the parent's floating
  atoms iff **`scope(child) > lower(child).size()`** (`computeUpperBound`). So an
  **inexact** child (lower empty) takes the parent's **whole** floating pool as
  its upper — *not* capped at the child's own scope — while an **exact** child
  (lower == scope) takes nothing new. The child's scope cap is a **formula**, not
  a tighter bound (probe B6: `for 4 A, 2 B`, B extends A → `B.upper = {A$0..A$3}`,
  the `#B ≤ 2` cap is a size formula). Getting this "can still grow" test wrong
  silently flips verdicts.
- **Size-formula guard (jar-verified, sharper than "lower==upper==n").** A size
  formula is emitted **iff `upper.size() > scope`** — i.e. only when the bound is
  looser than the scope. A plain top-level leaf whose `upper.size() == scope`
  gets **no** size formula (probe B1). Exact sigs always have `upper.size() ==
  scope`, so they never emit one. Shape (all quantified over atoms, never `#`):
  `scope 0 → no sig`; `scope 1 → lone sig` (inexact) / `one sig` (exact);
  `scope n≥2 inexact → no sig or (some v0..v_{n-1}: sig | v0+…+v_{n-1} = sig)` —
  the witnesses are **not** required disjoint, so the union is 1..n atoms, giving
  `#sig ≤ n` (probe B6). The exact n≥2 form adds pairwise-disjoint witnesses
  (`= n`) but is unreachable for prim sigs (exact ⇒ `upper == scope` ⇒ no
  emission).
- **Sibling disjointness is unconditional (jar-verified, probe B7).** `no (c_i &
  c_j)` is emitted for **every** sibling pair, even when the children's uppers are
  already disjoint (two exact children minting separate atoms still get the
  formula). The `<Sig>_remainder` relation does **not** participate in
  disjointness (probes B3/B4: only `no (B & C)`, never `no (B & remainder)`).
- **`one`-sig field owner-strip is `one`-only (jar-verified, probes B13/B14).** A
  field on a **`one`** sig stores only the value columns (arity = fieldArity − 1;
  `one sig B { f: A }` → `B.f` arity **1**, upper = `A`'s pool) and is decoded as
  `owner -> stored`. A **`lone`** sig's field is *not* stripped (`B.f` stays arity
  2 = `B -> A`). Field upper = product of the per-column sig uppers (probe B10:
  `B.f = B×A`; B12: an `Int` column → all 16 int atoms).
- **Exact (`=`) subset sig has no relation and no formula (jar-verified, probe
  B9).** `sig B = A + C` allocates **no** `B` relation and adds **no** formula; `B`
  denotes the union `A ∪ C`. An `in` subset gets a fresh relation + `B in A`
  (probe B8).
- **Multiplicity formulas (jar-verified).** `some sig` (lower empty) → `some sig`
  (probe B15). `one sig` is exact-1 bound-pinned → **no** formula (probe B13).
  `lone sig` that grows past scope 1 → the size path emits `lone sig` (probe
  B16); a top-level `lone` (upper ≤ 1) needs none.
- **Builtin bounds (jar-verified).** `Int` = exactly the integer atoms; `seq/Int`
  = exactly the first `maxseq` non-negative integer atoms (probe B18: `for 3` →
  `{0,1,2}`; no-overall → maxseq 4 → `{0,1,2,3}`). `String` = exactly empty
  (mettle mints no string atoms yet). The jar *also* builds `Int/min`, `Int/max`,
  `Int/next`, `Int/zero` ordering relations; these are **Rung-4** integer
  fidelity (pinned in [§12](#12-integer-builtin-relations-intminmaxnextzero-rung-4-mt-043))
  and mettle does not allocate them in Rung 3. `univ`/`none`
  are constants, never relations.

mt-030 (`als_core::bounds_builder::compute_bounds`) implements exactly this,
returning `Bounds` + a per-sig/field **denotation seam** (each sig/field's
`RelExprId`, so the leaf/remainder/union/subset shape is prebuilt for mt-031) +
the constraint `FormulaId`s. See `crates/als-core/tests/bounds.rs` for the pinned
tuple-set goldens.

---

## 2. Formula translation semantics

`TranslateAlloyToKodkod` is a bottom-up visitor over the resolved `Expr` tree
producing a Kodkod node of the matching sort (Formula / Expression /
IntExpression). This is exactly the three-sorted split mettle already has
(`als_core::ir::{Formula, RelExpr, IntExpr}`). The mapping (semantics, not Java
structure):

### 2.1 Relational expressions → `RelExpr`

| Alloy | Kodkod / mettle `RelExprKind` |
|---|---|
| sig / field / bound var | the allocated `Relation` / the bound `Variable` |
| `none` / `univ` / `iden` | `RelConst::{None, Univ, Iden}` |
| `+` `&` `-` `++` | `Union` / `Intersect` / `Diff` / `Override` |
| `.` (join) | `Join` |
| `->` (product; all 16 multiplicity arrows) | `Product` — the multiplicity (`some`/`one`/`lone` on either side) becomes an **added formula** (a per-column `some`/`one`/`lone` quantification, `ExprBinary` arrow case), not part of the product node |
| `~` transpose · `^` closure | `Transpose` / `Closure` (binary operands) |
| `*` reflexive-transitive closure | `Closure` unioned with `iden` restricted to `univ` (`RCLOSURE`) |
| `<:` domain / `:>` range restrict | product-pad the smaller side with `univ`, then intersect |
| `e'` (prime, temporal) | `Prime` |
| `{ x: A, … | φ }` comprehension | `Comprehension` (unary-bound decls + body formula) |
| `f ? e1 : e2` (relational ITE) | `IfThenElse` |
| `Int[ie]` | `IntToAtom` — `cint(e).toExpression()` |

### 2.2 Formulas → `Formula`

| Alloy | mettle `FormulaKind` |
|---|---|
| `!`/`not`, `&&`/`and`, `||`/`or`, `=>`/`implies`, `<=>`/`iff` | `Not` / `And` / `Or` / `Implies` / `Iff` (`and`/`or` are n-ary `ExprList`, built as a **balanced binary tree** by `getSingleFormula` — behaviorally associative, so mettle's flat n-ary `And`/`Or` is equivalent) |
| `in` / `=` (relational) | `RelCompare{Subset/Equal}` — but see the int special case below |
| `<` `>` `=<` `>=` (+ negated forms) | `IntCompare` (`typecheck_as_int` both sides) |
| `no`/`some`/`lone`/`one e` (multiplicity test) | `MultTest` |
| `all`/`some`/`no`/`lone`/`one x: B | φ` | `Quant` — see 2.3 |
| unary/binary temporal (`always`, `until`, …) | `TemporalUnary` / `TemporalBinary` |
| `disj[…]` | expands to pairwise `no (a & b)` conjunction (efficient staged form: `no(a&b) ∧ no((a+b)&c) ∧ …`) |
| `pred/totalOrder[elem, first, next]` | Kodkod native total-order predicate when the three args are plain relations (§5); otherwise a hand-built acyclic-order formula |

**Equality with integers.** `=`/`!=` translate to Kodkod set equality **unless
both sides are integer casts** (`IntToExprCast`), in which case they compare the
underlying int expressions. This is how a field of declared type `Int` compared
to an int literal (`a.n = 1`) type-checks and solves as an integer equality — the
resolution contract's "both sides `is_int`" case (resolution §4.5, probe 02).

### 2.3 Quantifiers & skolemization

- `no x | φ` ⇒ `all x | not φ`. `one`/`lone x | φ` are translated via cardinality
  of the matching set (a `some`/`lone` over the comprehension), not as primitive
  Kodkod quantifiers. `all`/`some` map to Kodkod `forAll`/`forSome`. A bare unary
  decl bound gets an implicit `one` (`addOne`), matching resolution §4.2.
- Multi-variable and multi-binding quantifiers desugar to nested single-variable
  quantifiers — exactly mettle's IR shape (`FormulaKind::Quant` over one `VarId`;
  ADR-0005 notes the desugar).
- **Skolemization is Kodkod's**, governed by `skolemDepth` (**default 0** =
  skolem **constants** only: a top-level `some x: A | φ` not under any `all`
  becomes a fresh unary constant relation; existentials under a universal are
  **not** skolemized at depth 0). Skolem relations appear in the decoded instance.
  **Naming:** `"$" + <name>` where `<name>` is `<cmdLabel>_<var>` when translating
  a command formula whose label has no `$` (e.g. `run foo { some x … }` →
  `$foo_x`), or `<funcName>_<var>` inside a function body, or just `<var>` when
  the enclosing command/func label already contains `$` (anonymous `run$2` →
  `$x`). (jar-verified: probe T9 — `run foo { some x: A | … }` → skolem `$foo_x`.)
  For **first-order** decls mettle skips skolemization entirely and quantifies
  directly (skolemization is an optimization + a nicer instance, never a verdict
  change) — see ADR-0011.
- **Higher-order decls are the exception (mt-038, §10.6):** a decl that ranges
  over *sub-relations* rather than tuples — a non-`one` unary marker (`some r: set
  A`), a multiplicity-marked arrow bound (`some f: A one -> one B`), or a run-pred
  param that is higher-arity or `set`/`some`/`lone`-marked — **cannot** be lowered
  first-order and is skolemizable *only* when it is an effective existential not in
  the scope of a universal (the depth-0 rule). mettle mints a fresh **free
  relation** `$<cmdLabel>_<var>` (lower `{}`, upper = the sound abstract upper of
  the decl bound's denotation), conjoins the decl's membership + multiplicity
  constraint (unary → `$r in bound` + `some`/`lone` test; arrow → the shared
  `arrow_value_constraint`), binds the var to that relation, and drops the
  quantifier. A HO decl that is **not** skolemizable (universal polarity, or under
  a universal) is what the jar's `HigherOrderDeclException` rejects — "Analysis
  cannot be performed since it requires higher-order quantification that could not
  be skolemized" — and mettle raises the same as a typed `TranslateError::
  HigherOrder`, never a wrong verdict. Full polarity rule + probes T9a–T9g in
  §10.6.

### 2.4 Integers, cardinality, `sum` — under overflow

- `#e` (cardinality) → `cset(e).count()` — a Kodkod `IntExpression`.
- `int[e]` / `sum e` (CAST2INT) → `e.sum()` — sums the integer *values* of the
  `Int` atoms in `e` (with `int[Int[x]] == x` shortcut).
- `Int[ie]` (CAST2SIGINT) → `ie.toExpression()` — the `Int` atom(s) for a value.
- `sum x: B | ie` → the Kodkod sum quantifier (mettle `IntExprKind::Sum`).
- The `fun/…` arithmetic (`plus`/`minus`/`mul`/`div`/`rem`, `IPLUS`/`IMINUS`/…)
  → the matching Kodkod `IntExpression` op (`plus`/`minus`/`multiply`/`divide`/
  `modulo`/`shl`/`shr`/`sha`). **The full per-op semantics (wraparound, div/rem
  sign conventions, div-by-zero, MIN/−1, shift kinds) and the exact forbid-mode
  polarity rule are pinned in the Rung-4 [§11](#11-integer-arithmetic-at-bitwidth-rung-4-mt-043).**
  Note the surface operators `+`/`-` are **relational** union/difference (`PLUS`/
  `MINUS` cases), never integer add — integer arithmetic is only ever the `fun/…`
  operator forms (`IPLUS`/`IMINUS`/`MUL`/…) (resolution §4.5, "no int↔Int
  coercion"). One real peephole exists, and it is on **`MINUS`**, not `IPLUS`
  (correcting an earlier note): `0 - (max+1)` folds to the constant `min` so the
  most-negative literal (`-8` at bw 4) can be written without an out-of-range
  intermediate (`TranslateAlloyToKodkod`, `ExprBinary` `MINUS` case).
- **Overflow semantics live entirely in Kodkod's int translation**, switched by
  `Options.setNoOverflow(opt.noOverflow)` and `IntEncoding.TWOSCOMPLEMENT` at the
  chosen bitwidth. With `noOverflow=false` (jar headless default) arithmetic
  **wraps** two's-complement; with `noOverflow=true` (Alloy GUI default; mettle's
  canonical default per **LEDGER-001**) any term whose result would exceed the
  bitwidth range **excludes that instance** (the `[AM]` overflow-preventing
  constraints). (jar-verified: probe T6 — `plus[7,7]=x` for `4 int` is **SAT**
  (wraps to −2) with overflow allowed, **UNSAT** with overflow forbidden.)
  Rung 3 defers full integer/counting fidelity to Rung 4 (ADR-0011); the overflow
  *switch* and its semantics are pinned here so Rung 4 implements one reference.
  **The forbid-mode constraint is polarity- and quantifier-sensitive (Milicevic/
  Jackson semantics), not a flat `∧ ¬overflow`; the exact rule is pinned in
  [§11.3](#113-forbid-mode-the-milicevicjackson-polarity-rule).**

### 2.5 Facts & command formula assembly

The final Kodkod goal is the conjunction of, in order:
1. all sig-hierarchy / subset / multiplicity / size constraint formulas added by
   `BoundsComputer` (§1.4);
2. every **fact** in every reachable module, including **synthesized** facts:
   sig **multiplicity** facts (`one`/`lone`/`some` sig), **field multiplicity**
   facts (a field decl `f: some B` adds `all this: S | some this.f`), **sig
   appended facts** (with `this` bound per resolution §3.3), and `util/*` module
   facts;
3. the **command formula**: for `run p` the pred body (params existentially
   quantified for a `run` of a function/pred with params); for `run {block}` the
   block; for `check a` the assertion body **negated** (`assertBody.not()`); for
   `check {block}` the block negated.
4. a reflexive `r = r` for every bounded relation, so Kodkod grows relations that
   the formula never mentions (a solving detail, not a semantic constraint).

For a `check`, **SAT means a counterexample was found** (the assertion can be
violated within scope); **UNSAT means the assertion holds** up to that scope.

---

## 3. Symmetry breaking

Alloy does **not** implement its own symmetry breaking — it sets Kodkod's
`Options.symmetryBreaking` to an integer and lets Kodkod's `SymmetryBreaker`
generate **lex-leader predicates** over the atom-permutation symmetries it detects
from the bounds. The integer is a **bound on the length of the generated
predicate** (a cost/completeness knob, not a count), default **20**.

- Higher values break more symmetry (faster on UNSAT, can slow SAT); `0` disables
  it entirely (raw satisfying assignments, no isomorph quotient).
- **The single most important, most surprising interaction:** Alloy forces
  `symmetry = 0` **whenever the command's `expect` is `1`**
  (`int sym = (expected == 1 ? 0 : opt.symmetry)` in `A4Solution`). So a command
  annotated `… expect 1` is solved with **no symmetry breaking**, changing the
  enumerated (SB-quotiented) instance count. (jar-verified: probe T3 —
  `run { some A } for 3` enumerates **3** instances with no `expect`, but **7**
  with `expect 1`, because 7 is the raw count of non-empty subsets of a 3-atom set
  and 3 is its symmetry quotient.) **This invalidates any conformance count run
  that ignores `expect`** — record alongside the mt-006 oracle gotchas.
- **Exact bounds already quotient symmetry.** When a relation is bound to an exact
  constant (integers, `util/ordering` first/next — §5), there is nothing left to
  permute on those atoms, so symmetry breaking is moot for them.

**What ADR-0002's counting config requires of mettle.** The canonical counting
net runs **both** sides at `symmetry = 0` (raw satisfying assignments), the only
regime where a count is solver-independent and comparable. mettle's early core has
**no symmetry breaking at all**, which *is* the `symmetry = 0` regime — so mettle
matches the jar's SB-0 count directly, with **no lex-leader machinery needed for
Rung 3**. Default-symmetry (SB=20) count parity is a later, dedicated net (it
requires bit-exact lex-leader predicate replication and is explicitly out of scope
per ADR-0002). Rung 3 ships **zero symmetry breaking** and is gauged on verdict +
SB-0 count.

---

## 4. Solving & outcome semantics

### 4.1 The SAT boundary

`A4Solution.solve` builds Kodkod `ExtendedOptions`: bitwidth (the command's, or
`ceil(log2(atoms+1))+1` when unset), `IntEncoding.TWOSCOMPLEMENT`, the symmetry
value (§3), skolem depth, overflow flag, trace bounds (temporal), and the solver
(SAT4J by default — pure Java, zero native deps, per the reference brief §4). It:

1. runs the default **`Simplifier`** (`inferPartialInstance = true`): a
   partial-instance pass that tightens bounds before solving (and can `shrink`
   `util/ordering` relations to exact — §5); if it proves the problem trivially
   false it adds `Formula.FALSE`.
2. conjoins all formulas into one goal (`fgoal`).
3. hands `(fgoal, bounds)` to the incremental solver's `solveAll` and peeks the
   first `Solution`.

Only **CNF-level** guarantees matter to mettle's own solver boundary
(`als_solve`): the translation from the bounded relational problem to CNF must be
**deterministic** (fixed variable numbering derived from the fixed atom order —
§1.3 — and fixed relation order — `RelId` order), so a fixed solver build gives
byte-identical output (ADR-0002 item 4; STYLE D1/D2). mettle does **not** need to
match Kodkod's CNF, only to be internally deterministic and to agree on the
verdict.

### 4.2 SAT → instance decoding

A `Solution` with a non-null Kodkod `Instance` is **SAT**. The instance maps each
bounded relation to a concrete `TupleSet`. Alloy decodes this (`A4TupleSet` /
`A4Tuple`) back to Alloy-level sig/field values, including **skolem** relations
(named per §2.3) and the pre-bound integer/string atoms. mettle's decoder
(`als-instance`, later) maps `als_solve::Assignment` → relation tuples →
sig/field/skolem values over the same `Universe`.

The instance is what a user sees for `run` SAT / `check` SAT (the
counterexample). Per ADR-0002 the tuples are **never** compared to the jar — only
verdict and (SB-0) count are.

### 4.3 UNSAT → "no counterexample / unsatisfiable"

A `Solution` with a null instance is **UNSAT**. For `run` this is reported as "no
instance found"; for `check` as **"no counterexample found — the assertion may be
valid (up to this scope)"** (the ROADMAP's "no counterexample" outcome). Unsat
cores are a solver-prover feature (out of the Rung-3 slice).

### 4.4 `expect` handling

`expect N` is normalized at resolve time to `-1/0/1` (resolution §3.6). It is
**not** part of the solve; it is a post-hoc check on the verdict:
`expect 1` asserts SAT, `expect 0` asserts UNSAT. The CLI treats a mismatch as an
error and exits non-zero (reference brief §5); the mt-006 harness mines `expect`
as "Net 0". **But** `expect 1` also silently sets `symmetry = 0` (§3) — so
`expect` is *not* verdict-only: it changes the SB-quotiented count. mettle must
mirror both effects.

### 4.5 Enumeration (`next` / distinct solutions)

Enumeration is the incremental SAT solver's job (`solveAll` returns a lazy
`Peeker<Solution>`; `A4Solution.next()` forks to the next). "Distinct solutions"
means **distinct Kodkod instances** — each `next()` adds a blocking clause that
rules out the current assignment, so the enumeration is over satisfying
assignments of the CNF, quotiented by whatever symmetry breaking is active. Hence:
- with `symmetry = 20` (default), the count is the **symmetry-quotiented** count;
- with `symmetry = 0`, the count is the **raw** satisfying-assignment count.

The pinned facts from mt-006's tests: `oracle/test1.als`'s `show` command at
`for 3` enumerates **87** instances at SB=20 and **1129** at SB=0. Enumeration is
"only implemented for MiniSat and SAT4J" (the incremental backends) — a
non-incremental solver throws on `next()`. mettle's `Solver` trait grows the
incremental/assumption interface for this (ADR-0005 item 6 anticipates it; block
each found model with a fresh clause).

---

## 5. `util/ordering` — exact bounds + symmetry special-casing (the Ledger corner)

This is the pending SEMANTICS_LEDGER corner ("`util/ordering` — the analyzer's
exact-bounds + symmetry special-casing"). It is realized at **two** levels, both
of which mettle must reproduce:

**(a) Exact scope on the ordered sig.** `module util/ordering[exactly elem]`
marks its parameter `exactly`. When a user writes `open util/ordering[A]`, that
`exactly` propagates so the instantiating sig `A` is added to the command's
`additionalExactScopes` — `ScopeComputer` then makes `A`'s scope **exact** (its
lower bound == upper bound == scope). So `open util/ordering[A]` + `for 3` gives
**exactly 3** `A` atoms, not ≤ 3. (jar-verified: probe T4 — atoms `A$0 A$1 A$2`.)

**(b) Exact bounds on `first`/`next` via the total-order predicate.** `util/
ordering`'s internal `Ord` sig carries an appended fact
`pred/totalOrder[elem, Ord.First, Ord.Next]`. `TranslateAlloyToKodkod` detects a
`pred/totalOrder` whose three arguments are plain relations and emits Kodkod's
**native total-order relation predicate** (`next.totalOrder(elem, first, last)`),
registering the four relations. The default `Simplifier` then **`shrink`s**
`first`/`last`/`next` to **exact constant bounds** derived from the (now exact)
atom order: `first = {elem$0}`, `last = {elem$last}`, `next = {elem$0->elem$1,
elem$1->elem$2, …}`. Additionally, `BoundsComputer` has a **direct** pre-binding
path for the *enum* case: a `one` sig with exactly two fields and a single
`pred/totalOrder` fact over an enum's children pre-binds `First`/`Next` to exact
constants without going through the predicate.

**Consequence pinned by probe:** an `open util/ordering[A]` + `for 3` model has
**exactly one** instance, and that count is **1 under both `symmetry=20` and
`symmetry=0`** — proving the uniqueness comes from the **exact bounds** on
first/next (which pin the atom order), **not** from symmetry breaking. (jar-
verified: probes T4, T4b — count=1 at sym 20 *and* sym 0.)

**IMPORTANT CAVEAT (mt-028 follow-up, jar-verified 2026-07-16, probe matrix
§10 dated entries below): this exact-constant pinning of `first`/`last`/`next`
holds only when the ordered sig `S` has no proper subsigs, or has subsigs whose
population is forced to coincide exactly with the whole of `S` (no genuine
partition choice remains).** The moment `S` has a proper subsig with a
non-exact scope, or **two or more** subsigs (even if each is individually
`exactly`-scoped), the exact-bounds shrink is **not applied** — `pred/
totalOrder` falls back to being solved as an ordinary Kodkod constraint, and
genuine, un-eliminated freedom remains in **which rank of the chain carries
which subsig tag** (this residual freedom is *not* removed by symmetry
breaking — compare sym20 vs sym0 counts in probes T14a/T14b below, which
differ by exactly the expected within-tag permutation factor, while the
across-tag rank freedom persists at both settings). Part (a) of the rule —
`S`'s **total** population being forced exact — is unaffected and holds
unconditionally in every subsig configuration tested. See the resolved
residual in §9 and the full matrix in §10 (probes T10–T19).

**Draft LEDGER entry** (for the human to approve; do not implement until
`approved`; this is the amended draft superseding the original — see
SEMANTICS_LEDGER.md LEDGER-004 for the formal amendment):

> ### LEDGER-004 — `util/ordering` exact bounds & order pinning (amended draft)
> **Rule:** Opening `util/ordering[S]` always forces sig `S`'s **total**
> population to be **exact** at whatever scope `S` resolves to (independent of
> whether the `for` clause uses `exactly`, of the multiplicity qualifier ---
> `one`/`lone`/`some` --- on `S`, and of whether `first`/`next`/`last`/`prev`
> are ever referenced by the command). **When `S` has no proper subsig, or has
> subsig(s) whose combined population is forced to equal all of `S` with no
> remaining partition choice**, the order's `first`/`last`/`next` relations are
> additionally bound to **exact constants** over `S`'s atoms in universe order
> (`first = S$0`, `last = S$<n-1>`, `next` = the consecutive-atom successor
> relation) --- the linear order is then fully pinned, independent of the
> symmetry-breaking setting. **When `S` has a proper subsig with non-exact
> scope, or two-or-more (even fully exact) subsigs, this second half does
> *not* apply**: `first`/`next`/`last` remain governed only by the ordinary
> `pred/totalOrder` constraint, and genuine order freedom (which rank holds
> which subsig tag) survives as multiple distinct satisfying instances, at
> every symmetry-breaking setting.
> **Status:** proposed (amended). **Evidence:** probes T4/T4b (original) plus
> the mt-028 matrix T10-T19 (§10) — count=1 at symmetry 20 and 0 for a
> childless ordered sig at sizes 2-6, two independent ordered sigs, an enum,
> and a fully-collapsed subsig; count > 1 at both symmetries (with sym0 always
> a multiple of the sym20 count, by the expected leftover permutation factor)
> whenever the ordered sig has a genuine subsig partition choice. **Test:**
> _(added with the Rung-3 ordering work)_.

Rung 3's vertical slice includes `util/ordering` (it appears throughout the
corpus); the general non-enum total-order path (no subsigs) is the common
case and the one to implement first. mettle must also implement the subsig
fallback path (real `pred/totalOrder` solving, not shrink) faithfully rather
than assuming the shrink always applies — the corpus almost certainly contains
ordered sigs with subsigs (e.g. temporal/state-machine idioms), and pinning
the wrong path would silently under- or over-count instances.

---

## 6. Self-verification (the ROADMAP's "self-verified" promise)

`A4Solution.eval(Expr)` translates an expression against a **solved, satisfiable**
instance (`TranslateAlloyToKodkod.alloy2kodkod` in an evaluation mode) and
evaluates it to a tuple set, an `Integer`, or a `Boolean` over the found instance.
This is exactly mettle's self-check net (ADR-0002 item 2 — "instance validity is
checked by our own evaluator, not by the jar"): after finding an instance, mettle
**evaluates the command's full formula (all facts ∧ the command formula) against
that instance and asserts it evaluates to `true`**. A found instance that fails
its own formula is a mettle bug (a hard `debug_assert!`), never a user error.
This gives Rung 3 its "self-verified" property without ever diffing the jar's
tuples: mettle trusts an instance only when its own evaluator confirms it.

The evaluator is also the substrate for the future REPL (Rung 5) and for
`check`-counterexample explanation. For Rung 3 it need only cover the operators a
solved model uses (the same three-sorted evaluation, over concrete `TupleSet`s).

---

## 7. Gotchas / dark corners (verify against the jar before implementing)

1. **`expect 1` disables symmetry breaking** (`sym = expected==1 ? 0 : 20`).
   Verdict-only reasoning about `expect` is wrong; it changes the count. (T3)
2. **Overflow default is entry-point-dependent** (reference brief §3(c),
   LEDGER-001): headless/API default = allow (wrap); GUI default = forbid; mettle
   canonical = **forbid**. Always set it explicitly. (T6)
3. **Atom names are `Name$index`, plain decimal, no zero-padding** (despite the
   source comment). Ints are their decimal value; both are the exact `Universe`
   order (sigs, then ints ascending, then strings). (T1, T2, T8)
4. **`for N` on an abstract parent does not cap the sum of its children** — each
   top-level/derived child gets its own scope. Only the abstract-scope derivation
   (all-children-scoped) sums them. (T5)
5. **A `one` sig's field relation stores the field value re-multiplied by the
   sig** (mutable-singleton safety) — the decoded field is `sig -> storedRel`.
6. **`util/ordering` pins order via exact bounds, not symmetry breaking** — a
   single instance even at `symmetry = 0`. (T4, T4b)
7. **`pred/totalOrder` has two translations**: Kodkod-native (all-relation args →
   exact-bound-able) vs. a hand-built acyclic formula (non-relation args). Only
   the first gets exact bounds.
8. **The `run`/`check` default scope is identical (overall 3)** — no branch on
   command kind. (T1)
9. **Skolem constants only at depth 0**: existentials under a universal are not
   skolemized; skolem relation name is `$<cmdOrFunc>_<var>` (or `$<var>` when the
   label has a `$`). (T9)
10. **A `check` reports SAT as "counterexample found"** (negated assertion), the
    inverse of `run` — get the user-facing polarity right.
11. **Non-incremental solvers cannot enumerate** — `next()` throws. Enumeration
    needs the incremental interface (SAT4J/MiniSat).

---

## 8. Determinism notes

The reference is deterministic here because the universe atom list, the bounds
map, and the relation order are all built in fixed (declaration/scope) order.
mettle mirrors this (STYLE D1/D2, already enforced by the `als-core` skeleton's
`BTreeMap`/`BTreeSet` bounds and append-only arenas):
- **Atom order** is fixed by §1.3 (sigs in declaration order → atoms in index
  order → ints ascending → strings) — the one canonical order for CNF variable
  numbering.
- **Relation order** is `RelId` allocation order (lowering order = resolved
  source order).
- **CNF variable/clause numbering** is insertion order (`als_solve::Cnf` already
  asserts dense, insertion-order numbering).
- Nothing near numbering/output may iterate a hash map (STYLE D2). The jar's own
  `IdentityHashMap`/`LinkedHashMap` uses are membership-only or already
  insertion-ordered; mettle uses typed-ID arenas and BTree maps.

mettle's determinism contract (ADR-0002 item 4) is **self-consistency for a fixed
build** (byte-identical output/enumeration order across runs/machines) — *not*
matching Kodkod's CNF or enumeration order, which is impossible and not attempted.

---

## 9. Open questions / residual uncertainty (be honest)

- **RESOLVED (mt-028, 2026-07-16):** the general (non-enum) `util/ordering`
  exact-shrink's precise `next` constant for orders of size 2 through 6 is now
  jar-verified — always the plain consecutive chain `S$0->S$1->...->S$<n-1>`,
  `first=S$0`, count=1 at both symmetry 20 and 0 for every size (probes
  T10a-T10e, §10). **Also resolved: the interaction with a partially-scoped
  (subsig'd) ordered sig — and the answer is a genuine correctness corner, not
  a non-issue.** When the ordered sig has a proper subsig with non-exact scope,
  or two-or-more subsigs (even individually `exactly`-scoped), the exact-bounds
  shrink does **not** engage: `pred/totalOrder` is solved as an ordinary
  constraint and real, symmetry-surviving freedom remains in which chain rank
  carries which subsig tag (probes T11a-T11e, §5, §10). This is now folded into
  the amended LEDGER-004 draft (§5) rather than left open — mettle's Rung-3
  ordering implementation must special-case this (detect whether `S`'s
  population resolves to a single determinate set before applying the
  exact-shrink optimization; fall back to genuinely solving the total-order
  constraint otherwise).
- **Skolemization** is pinned structurally (depth-0 constants, `$name` naming) but
  mettle may skip it for the Rung-3 slice (quantify directly); if kept-out, note
  in LIMITATIONS that instance skolem relations won't match the jar's shape (they
  never affect the verdict). **UPDATE (mt-043):** the first-order skolemization
  rule (naming, depth-0 gate, nesting, SB-0 count effect) is now fully pinned in
  [§15](#15-first-order-skolemization-rung-4-mt-043) so mt-047 can make the
  `skip_fo_skolem` counting family exact; mt-038 already implemented the
  higher-order half (§10.6).
- **The `Simplifier` / `inferPartialInstance`** does more than the ordering shrink
  (general partial-instance inference); its full behavior was not pinned because
  it is a **performance** pass that cannot change the verdict (it only tightens
  bounds a sound solve would respect anyway). mettle may ship Rung 3 without it.
- **RESOLVED (mt-043, 2026-07-18):** integer/bitwidth fidelity beyond the overflow
  switch (division/remainder rounding + sign, div-by-zero, MIN/−1, shifts, `sum`,
  integer if-then-else, `#` cardinality overflow, the `Int/min|max|next|zero`
  builtin relations, `seq/Int` bounds, `seq` field desugar) is now pinned in the
  Rung-4 sections [§11](#11-integer-arithmetic-at-bitwidth-rung-4-mt-043)–[§14](#14-seq-semantics-rung-4-mt-043)
  with the probe matrices [§10.7](#107-mt-043-integer-arithmetic--overflow-probes-jar-verified-2026-07-18)–[§10.10](#1010-mt-043-seq-probes-jar-verified-2026-07-18).
- **Temporal solving** (`var`, `always`/`until`, trace scopes, the `[electrum]`
  Pardinus paths) is Rung 6; §1/§2 note where it diverges (temporal disjointness
  formulas, `maxtrace`/`mintrace`, `Prime`) but the bounded LTL→FOL expansion is
  out of scope here.
- **CNF-level count parity at default symmetry (SB=20)** is deliberately *not*
  pinned — it needs bit-exact lex-leader replication and is a later dedicated net
  (ADR-0002). Rung 3 gauges verdict + SB-0 count only. **UPDATE (mt-043):** the
  SB=20 posture (what the "20" is, what it changes, why it never flips a verdict)
  is pinned in [§16](#16-symmetry-breaking-posture-rung-4-mt-043) as the input to
  ADR-0012's posture decision.

Anything this document leaves ambiguous: **test against the jar first** (extend
the §10 probe harness), record the answer here or in SEMANTICS_LEDGER.md, then
implement.

---

## 10. Probe log (jar-verified 2026-07-16)

Harness: `scratchpad/probe/ProbeT.java` — drives `TranslateAlloyToKodkod.
execute_command` via the `A4Options` API (never the `exec` CLI, whose
`-y`/`--ymmetry` flag is a no-op, reference brief §3(c)); prints, per command,
the normalized command string, `expects`, the SAT/UNSAT verdict, the enumerated
instance count (capped or exhaustive), and the instance's non-builtin atoms.
Oracle: `oracle/org.alloytools.alloy.dist.jar` (6.2.0), OpenJDK 21. Where source
and jar could differ, **the jar wins** (none diverged).

| # | Case | Verdict / observation |
|---|---|---|
| T1 | bare `run {}`, `run { some A }`, `check {…}` (sig A, sig B{f:A}) | all resolve at overall scope **3**; sig atoms named `A$0`, `B$0 B$1 B$2`; `run`/`check` identical scope |
| T2 | `run { some A } for 2 but exactly 4 A` | **4** exact A atoms `A$0 A$1 A$2 A$3` — `exactly` overrides `for 2` |
| T3 | `run { some A } for 3` vs `… expect 1`, exhaustive | **3** instances without `expect`; **7** with `expect 1` → **`expect 1` sets symmetry=0** |
| T4 | `open util/ordering[A]`, `sig A`, `for 3`, exhaustive, sym 20 | **count=1**; atoms `A$0 A$1 A$2 ordering/Ord$0` — ordered sig forced **exact** 3 |
| T4b | same as T4 at **symmetry 0** | **count=1** still → uniqueness is from **exact bounds on first/next**, not symmetry breaking |
| T5 | `abstract sig A`, `B extends A`, `C extends A`, `for 4` | SAT; each child scoped 4 independently (abstract `for N` does not cap the sum) |
| T6 | `run { some a: A | plus[7,7] = a.x } for 3 but 4 int` | **SAT** with `noOverflow=false` (7+7 wraps to −2); **UNSAT** with `noOverflow=true` |
| T8 | `run { #A = 2 } for 3` + `univ` dump | SAT; `univ={A$0, -8, -7, …, 7}` — sig atoms then ints ascending; cardinality works |
| T9 | `run foo { some x: A | x=x } for 3`, instance dump | skolem relation **`$foo_x`** = `{A$0}` |

### 10.1 LEDGER-004 exhaustive probe matrix (mt-028, jar-verified 2026-07-16)

Harness: `LedgerShim.java` (scratchpad, modeled on `crates/als-conform/shim/
OracleShim.java` and the T-series `ProbeT.java`) — drives `TranslateAlloyToKodkod.
execute_command` via `A4Options`, dumps `A4Solution.toString()` (every relation's
exact tuple set, including private stdlib relations like `ordering/Ord<:First` /
`ordering/Ord<:Next`) for the first few satisfying instances of each command, plus
the exhaustive enumerated instance count. Every case run at **both**
`symmetry=20` and `symmetry=0`; `noOverflow=false`; solver `sat4j`; `expect` never
used (it silently forces `symmetry=0`, reference brief gotcha). Clean-room:
behavior probed black-box only; no upstream `.als` module text was newly read for
this pass (the `Ord`/`First`/`Next`/`pred/totalOrder` names were already public
knowledge from this document's existing §5 prose).

| # | Case | sym20 count | sym0 count | Observation |
|---|---|---|---|---|
| T10a-e | `open util/ordering[S]; sig S {}; run {} for N S`, N=2..6, exhaustive | **1** (all N) | **1** (all N) | `next` is always the plain consecutive chain `S$0->S$1->...->S$<N-1>`, `first=S$0`; matches original T4/T4b at every tested size |
| T10f | same shape + unrelated `sig T {}` (`for 3 S, 2 T`), vs. control with `open` removed | **3** both | **4** both | S/T counts identical with and without the `open` → ordering contributes exactly a **1x multiplier**, independent of unrelated sigs' own DOF and of the symmetry setting |
| T11 (scope forms) | default scope (no `for`); `for N S`; `for exactly N S`; overall-only `for 4`; `for 1 S` | all **1** | all **1** | `exactly` keyword is redundant — ordering forces exactness regardless; `for 1 S` gives a valid degenerate order (`first=last=S$0`, `next={}`) |
| T11b | `one sig S {}` vs `lone sig S {}` (no `for`) | both **1**, `S={S$0}` | both **1** | **`lone`'s default derived scope collapses to 1** (not the overall default 3) per §1.2's "forces...lone sig to ≤1" — so no conflict with the ordering's exactness ever arises; not a counterexample, just confirms scope derivation happens before exactness is applied |
| T11c | `some sig S {}`, `for 3` | **1** | **1** | `some` doesn't cap below the default scope — behaves like a plain sig |
| T12 | two independent opens: `open util/ordering[A] as ordA`, `open util/ordering[B] as ordB`, `for 3 A, 4 B` | **1** | **1** | both orders pinned fully independently; `ordA/Ord<:First`, `ordB/Ord<:First` etc. all present and separately exact |
| T13 | `enum Color {Red,Blue,Green}`, bare `run {}` | **1** | **1** | enum auto-opens ordering; `First=Red$0` (first **declared** constant), chain `Red->Blue->Green` — same exact-constant pinning as an explicit sig |
| **T14a** | ordered `sig A {}` + non-exact child `sig B extends A {}`, `for 3 A, 2 B` | **7** | **42** | **COUNTEREXAMPLE to the unqualified rule.** Same literal atom-name population appears with genuinely different `next`-chain shapes across instances (e.g. `A0->A1->B0` vs `A0->B0->A1` for identical `this/A`/`this/B`) — real order freedom, not a naming artifact. 7 = choose-which-ranks-are-B, `C(3,0)+C(3,1)+C(3,2)`; 42 = 7 × (3-choose-2 residual atom-identity permutations at sym0) |
| **T14b** | same shape but child forced **exactly** 1: `for 3 A, exactly 1 B` | **3** | **6** | Isolates rank-freedom from population-freedom: **all 3 instances have the identical atom-name population** `{A$0,A$1,B$0}`, yet `B$0` occupies rank 1, 2, and 3 respectively across the 3 solutions. Proves the freedom is in the **order itself**, not in subsig membership size. 3 = `C(3,1)`; 6 = 3 × 2! (sym0 restores the within-tag atom-permutation freedom too) |
| **T14c** | `abstract sig A {}`, `sig B,C extends A {}`, both children **exactly** scoped: `for 3 A, exactly 2 B, exactly 1 C` | **3** | (not run) | Even with **every** child individually exact, ≥2 children still leaves rank-tagging freedom: `C(3,1)=3` |
| **T14d** | `abstract sig A {}`, `B,C extends A {}`, both children **non-exact**, `for 4 A` | **384** | **9216** | Large residual freedom (membership size × rank choice, both free) — matches original T5's "children scoped independently" plus the new rank-freedom on top |
| **T14e** | degenerate collapse: single child forced to equal the **whole** of A: `for 3 A, exactly 3 B` (B≡A always) | **1** | (not run) | Pinning **re-engages** once there is no genuine partition choice left — atoms display as `B$0..B$2` (child's name wins in output) but the order is unique again |
| T15 | control: **unrelated** field (not a subsig) `sig T { f: S }`, `for 3 S, 2 T` | **10** | **16** | A field reference to `S` from an unrelated sig does **not** disturb `S`'s own pinning — `ordering/Ord<:Next` stays exactly `S$0->S$1->S$2` in every enumerated instance; only `T`'s field assignment contributes the extra count. Isolates the T14 effect to **subsig partitioning specifically**, not "any relation touching S" |
| T16 | `fact { #first.^next = 0 }` (contradicts the real 2-successor first, `for 3 S`) | **UNSAT** | — | Proves `first` is a genuine hard-bound constant, not a solver preference — no alternate atom can be chosen to dodge the fact |
| T16b | `fact { #first.^next = 2 }` (consistent), `for 3 S` | **SAT, count=1** | — | Trivial positive control for T16 |
| T17 | `fact { #S = 5 }`, `for 3 S` (ordering forces exact 3) | **UNSAT** | — | Behaves exactly like an ordinary `exactly`-scope/fact conflict — plain UNSAT, no special diagnostic; same code path as any other over-constrained exact scope |
| T18 | `var sig S {}` + `open util/ordering[S]` | — | — | **Rejected before solving** (parse/resolve stage): `"Module util/ordering forces parameter to be exact but this/S variable."` — clean structural reject, not a silent accept or a solve-time surprise |
| T19 | `open util/ordering[S]; sig S {}; run { some S }` (first/next/last never referenced) vs. same file without the `open` | **1** vs **3** | **1** vs **7** | Merely **opening** the module — with zero references to `first`/`next`/`prev`/`last` in the command — still collapses the count to the T4-style single instance. The pinning is triggered by the `open` (the private `Ord` sig's appended `pred/totalOrder` fact existing in the world), **not** by any use of the ordering functions |

Anything this document leaves ambiguous: **test against the jar first** (extend
`ProbeT`/`LedgerShim`), record the answer here (verdict/count) or in
SEMANTICS_LEDGER.md (behavior), then implement.

### 10.2 mt-030 bounds probe matrix (jar-verified 2026-07-16)

Harness: `scratchpad/probe/BoundsShim.java` (dumps `A4Solution.getBounds()` per
relation as name-tuples) and `edu.mit.csail.sdg.translator.DumpK2` (dumps
`A4Solution.debugExtractKInput()` — the exact Kodkod formula + bounds as
originally built). Both run at `symmetry=0`, `noOverflow=false`, and
**`inferPartialInstance=false`** so the raw `BoundsComputer` output is seen
before the `Simplifier` inlines derived relations (with inference *on*, subset/
field relations read back `null` after solve — the reason the raw dump is
needed). The pinned facts are folded into §1.4′ above; each maps to a committed
golden in `crates/als-core/tests/bounds.rs`.

| # | Case | Pinned observation |
|---|---|---|
| B1 | `sig A {} run {} for 3` | `A` lower `{}`, upper `{A$0,A$1,A$2}`; **no** size formula (upper == scope) |
| B2 | `for exactly 3 A` | `A` lower == upper == `{A$0..A$2}`; no formula |
| B3 | `sig A {} sig B extends A {}` | no `A` relation; `A_remainder` + `B` both upper `{A$0..A$2}`; no disjointness (1 child), no size |
| B4 | + `sig C extends A {}` | `B`,`C`,`A_remainder` upper `{A$0..A$2}`; one formula `no (B & C)` (remainder excluded) |
| B5 | `abstract sig A` + B,C | no `A`, **no `A_remainder`**; `no (B & C)` only |
| B6 | `for 4 A, 2 B` (B extends A) | `B.upper = {A$0..A$3}` (whole pool, not 2); size formula `no B or (some v1,v0: B \| v1+v0 = B)` |
| B7 | `for exactly 2 B, exactly 1 C` (disjoint uppers) | still emits `no (B & C)` — disjointness is **unconditional** |
| B8 | `sig B in A {}` | fresh `B` lower `{}` upper `{A$0..A$2}`; formula `B in A` |
| B9 | `sig B = A + C {}` | **no** `B` relation, **no** formula; `B` denotes `A ∪ C` |
| B10 | `sig B { f: A }` | `B.f` arity 2, upper `B × A` (9 tuples), lower `{}` |
| B11 | `sig B { f: A -> A }` for 2 | `B.f` arity 3, upper `B×A×A` (8 tuples) |
| B12 | `sig A { n: Int }` | `A.n` arity 2, upper `A × {all 16 int atoms}` |
| B13 | `one sig B { f: A }` | `B.f` arity **1** (owner stripped), upper `{A$0..A$2}`; `B` pinned `{B$0}`; field denotes `B -> B.f`; no `one B` formula |
| B14 | `lone sig B { f: A }` | `B.f` arity **2** = `B × A` — the strip is `one`-only |
| B15 | `some sig A {} for 3` | formula `some A` (the only one; size guaranteed by bound) |
| B16 | `lone sig B extends A {}` for 3 | `B` grows to `{A$0..A$2}`, scope 1 → size path emits `lone B` |
| B17 | any command, `Int` | bound exactly to the 16 int atoms `{-8..7}` |
| B18 | `seq/Int` | `for 3` → `{0,1,2}`; no-overall (maxseq 4) → `{0,1,2,3}` |
| B19 | `sig P {} sig C extends P {} run {} for exactly 2 P, exactly 3 C` | **accepted, SAT** — `ScopeComputer.computeLowerBound` silently *raises* `P`'s scope to the children's lower sum (2→3, exactness kept, §1.2); universe `{C$0,C$1,C$2}`, `P_remainder` upper empty, Kodkod goal = bare reflexive list (no size formula). Found in mt-030 review (tech lead); fixed in mt-029's walk (`scope.rs`), regression tests in `tests/scope.rs` + `tests/bounds.rs` |

### 10.3 mt-031 lowering probe matrix (jar-verified 2026-07-16)

Harness: `scratchpad/probe/DumpK2.java` (`edu.mit.csail.sdg.translator.DumpK2`)
prints `A4Solution.debugExtractKInput()` — the **exact final Kodkod goal
formula** for a command — at `symmetry=0`, `noOverflow=false`,
`inferPartialInstance=false`. For ~15 small models spanning the §2 tables the
dump was compared to mettle's lowered IR (`crates/als-core/tests/lower.rs`,
which quotes each jar formula and asserts semantic congruence). The pinned
facts below sharpen §2/§2.5; each maps to a committed golden.

**Documented divergences (semantic congruence, not identity)** — mettle's IR is
equal to the jar's goal *modulo*: (a) **no skolemization** (mettle quantifies
directly; ADR-0011); (b) **n-ary vs balanced-binary `and`/`or`** (§2.2, the jar
builds a left-nested binary tree, behaviorally associative); (c) **no reflexive
`r = r` padding** (§2.5(4), a Kodkod solving detail, mt-033's job); (d) mettle
**groups a field's domain + multiplicity constraints into one conjunct** where
the jar emits them separately; (e) mettle **omits the jar's redundant
per-arrow-column membership constraints** (`(v.f) in A`), which are entailed by
the top-level `this.f in (A->B)`.

| # | Case | Jar goal (relevant conjunct) | Pinned fact |
|---|---|---|---|
| L1 | `sig B { f: A }` (default field) | `all this: B \| one (this.f) and (this.f) in A` | a **default** (unmarked) unary field bound gets an **implicit `one`** plus bound-membership |
| L2 | `f: set A` | `all this: B \| (this.f) in A` | `set` → membership only, no multiplicity |
| L3 | any field | `(f . univ…) in owner` | every field also emits a **domain** constraint: the first column ⊆ owner (join `univ` `arity-1` times to project); mt-030's bounds do **not** emit this, so the lowerer owns it (no double-count) |
| L4 | `f: A -> one A` | `all this: B \| (this.f) in (A->A) and (all v0: A \| one (v0.(this.f)) and (v0.(this.f)) in A) and (all v1: A \| ((this.f).v1) in A)` | a single arrow `A m -> n B` → membership `this.f in A->B` **plus per-column** `all a: A \| n (a.this.f)` and `all b: B \| m ((this.f).b)`; a `set`/absent column marker adds no cardinality. The per-column memberships are redundant (entailed) and mettle omits them |
| L5 | `sig A { r: set A, s = r }` (defined field) | `all this: A \| (this.s) = (this.r)` | a defined field `f = e` → `all this: S \| this.f = e[this]` |
| L6 | `sig A {…}{ φ }` (appended fact) | `all this: A \| φ` | a sig appended fact is universally quantified over the owner, with `this` bound to it (resolution §3.3) |
| L7 | `a.n = 1`, `n: Int` | `(a.n) = Int[1]` | the **integer special case** (§2.2): a `=`/`in` with **one** small-int side (the literal `1`) and a relational side promotes the small-int via `Int[·]` (`IntToAtom`) and does a **set** compare; only when **both** sides are small-int casts (`#x = #y`, `int[x]=int[y]`) is it an `IntCompare` |
| L8 | `pred sub[x] {…}` `… sub[a] …` | the call vanishes; body inlined with `x ↦ a` | a func/pred call is **inlined** (params substituted by the lowered args, a receiver by the caller's `this`); recursion is refused (`TranslateError::LoweringUnsupported`) |
| L9 | `check a` (assert `a`) | `assertBody.not()` | a `check` **negates** the assertion body (SAT = counterexample); a block `check` negates the block; a `run` pred existentially quantifies its params (`some x: B \| body`) |
| L10 | `a.*nx` | `nx + (iden restricted)` closure | `*` = reflexive-transitive closure (IR `ReflexiveClosure`); `^`/`~` map to `Closure`/`Transpose` |
| L11 | `A <: f` / `f :> A` | product-pad-and-intersect | `A <: r` = `r & (A -> univ^{n-1})`; `r :> A` = `r & (univ^{n-1} -> A)`; a **unary** `r` reduces both to `r & A` (jar-consistent) |
| L12 | `one sig Cfg { limit: one A }` | field relation `Cfg -> Cfg.limit` | a **`one`-sig** field is denoted `owner -> stored` (mt-030 seam), so `this.f` and a bare `Cfg.limit` both join the singleton owner back on (§1.4′ B13) |
| L13 | `all disj x, y \| φ` | disjointness guard | a decl `disj` modifier adds pairwise `no (xi & xj)`: an **antecedent** for `all`/`no`, a **conjunct** for `some` and inside `one`/`lone`'s comprehension; `no x \| φ` ⇒ `all x \| ¬φ`; `one`/`lone x \| φ` ⇒ `one`/`lone { x \| φ }` (§2.3) |
| L14 | `disj[A, B, C]` | `no (A&B) and no ((A+B)&C)` | the `disj[…]` builtin expands to the **staged** pairwise form (§2.2) |
| L15 | `sig S { disj a, b: set E }` (2-field group) | `no (this/S.a & this/S.b)` | a pre-colon **field-group `disj`** adds one `no (fi & fj)` conjunct over the **full field relations** — emitted **after both fields' mult+domain facts** and before the command formula (jar-verified probe p1, mt-038) |
| L16 | `disj a, b, c: set E` (3-field group) | `no ((this/S.a + this/S.b) & this/S.c) and no (this/S.a & this/S.b)` | the group takes the **staged** pairwise form (same shape as `disj[…]`, L14): stage `k` forbids `f_k` from meeting `f_0+…+f_{k-1}`. mettle emits the same conjuncts in incremental order (`no(a&b) and no((a+b)&c)`; §10.3 divergence (b), `and` associative) (probe p2) |
| L17 | `disj f, g: E -> E` (arity-2 group) | `no (this/S.f & this/S.g)` | disjointness is over the **whole** (arity-3) field relations, independent of the field arity (probe p3) |
| L18 | `disj a, b: E` (implicit-`one` group) | `no (this/S.a & this/S.b)` | the per-field implicit `one` (L1) does not change the disj fact (probe p4) |
| L19 | `var disj a, b: set E` (var group) | `always (no (this/S.a & this/S.b))` | a **`var`** group wraps each `no` in `always` — temporal, so mettle **defers** the whole command (`TranslateError::TemporalUnsupported`, §2.3), never a silent drop (probe p5) |

**mt-039 nested-arrow field-bound probes (jar-verified 2026-07-17, probes n1–n7,
`scratchpad/probe/nested/n1..n7`).** `arrow_field_constraint` (§2.1's L4 row)
previously handled only a **flat** binary arrow `A m -> n B`; any arrow with a
side that is itself an arrow (`f: A -> (B one -> one C)`, `f: (A -> B) one ->
one C`, …) hit a typed defer. Probes n1–n7 (all `sig A {} sig B {} sig C {}
sig S { f: <bound> } run {} for 3`; n6 adds `sig D {}`) pin the reference's
recursive per-column translation, `DumpK2`, symmetry 0, noOverflow false,
`inferPartialInstance` false, `this/X` shortened to `X` and multi-line dumps
compacted to one line (same convention as L1–L19; no other change):

| # | Case | Jar goal (relevant conjunct) | Pinned fact |
|---|---|---|---|
| L20 | n1: `f: A -> (B one -> one C)` (right-nested, inner marked) | `all this:S \| (this.f) in (A->(B->C)) and (all v0:A \| (v0.(this.f)) in (B->C) and (all v1:B \| one(v1.(v0.(this.f))) and (v1.(v0.(this.f))) in C) and (all v2:C \| one((v0.(this.f)).v2) and ((v0.(this.f)).v2) in B)) and (all v3:univ,v4:univ \| ((v4->v3) in (B->C) and (all v5:B \| one(v5.(v4->v3)) and (v5.(v4->v3)) in C) and (all v6:C \| one((v4->v3).v6) and ((v4->v3).v6) in B)) implies (((this.f).v3).v4) in A)` | a side that is itself an arrow **recurses fully** (the `all v0:A` block re-derives the nested type's own membership + per-column tests on the joined remainder) rather than testing one multiplicity; the trailing `v3,v4` block is the outer (unmarked) column and is **fully redundant** (its only consequent is bare membership in `A`, entailed by the top membership at any recursion depth) — mettle omits it entirely (divergence (e) generalized) |
| L21 | n2: `f: A one -> (B -> C)` (outer marked, plain inner) | `all this:S \| (this.f) in (A->(B->C)) and (all v0:A \| (v0.(this.f)) in (B->C)) and (all v1:univ,v2:univ \| (v2->v1) in (B->C) implies (one(((this.f).v1).v2) and (((this.f).v1).v2) in A))` | the inner `B->C` is flat/unmarked so its own column tests are empty (only the redundant-but-harmless recursive membership survives, kept per the existing L4 policy of never omitting a recursive call's own top membership); the outer `one` lands on the **left** column, which must destructure the compound RHS `(B->C)` into fresh `univ` leaves (`v1,v2`) since Kodkod has no single named relation to decl-bind against a literal product |
| L22 | n3: `f: (A -> B) one -> one C` (left-nested) | `all this:S \| (this.f) in ((A->B)->C) and (all v0:univ,v1:univ \| (v0->v1) in (A->B) implies (one(v1.(v0.(this.f))) and (v1.(v0.(this.f))) in C)) and (all v2:C \| one((this.f).v2) and ((this.f).v2) in (A->B))` | the compound **LHS** is destructured for the right (`rhs_mult`) column exactly as a compound RHS would be (§10.3's arrow recursion is symmetric in which side is compound); the left (`lhs_mult`) column iterates the plain `C` directly, decl-bound as usual |
| L23 | n4: `f: A -> (B some -> lone C)` | `all this:S \| (this.f) in (A->(B->C)) and (all v0:A \| (v0.(this.f)) in (B->C) and (all v1:B \| lone(v1.(v0.(this.f))) and (v1.(v0.(this.f))) in C) and (all v2:C \| some((v0.(this.f)).v2) and ((v0.(this.f)).v2) in B)) and (all v3:univ,v4:univ \| ((v4->v3) in (B->C) and (all v5:B \| lone(v5.(v4->v3)) and (v5.(v4->v3)) in C) and (all v6:C \| some((v4->v3).v6) and ((v4->v3).v6) in B)) implies (((this.f).v3).v4) in A)` | `some`/`lone` map through the recursion exactly like `one` (L20) — the column-to-test mapping (`rhs_mult` tested over the LHS's tuples, `lhs_mult` over the RHS's) is unchanged by nesting depth; the trailing `v3,v4` block is again fully redundant (outer unmarked) and omitted |
| L24 | n5: `f: A lone -> (B -> C)` (mirrors n2 with `lone`) | `all this:S \| (this.f) in (A->(B->C)) and (all v0:A \| (v0.(this.f)) in (B->C)) and (all v1:univ,v2:univ \| (v2->v1) in (B->C) implies (lone(((this.f).v1).v2) and (((this.f).v1).v2) in A))` | confirms L21's shape generalizes to every `Mult` variant, not just `one` |
| L25 | n6: `f: A -> (B -> (C one -> one D))` (three levels) | `all this:S \| (this.f) in (A->(B->(C->D))) and (all v0:A \| (v0.(this.f)) in (B->(C->D)) and (all v1:B \| (v1.(v0.(this.f))) in (C->D) and (all v2:C \| one(v2.(v1.(v0.(this.f)))) and (v2.(v1.(v0.(this.f)))) in D) and (all v3:D \| one((v1.(v0.(this.f))).v3) and ((v1.(v0.(this.f))).v3) in C)) and (all v4:univ,v5:univ \| ((v5->v4) in (C->D) and (all v6:C \| one(v6.(v5->v4)) and (v6.(v5->v4)) in D) and (all v7:D \| one((v5->v4).v7) and ((v5->v4).v7) in C)) implies (((v0.(this.f)).v4).v5) in B)) and (all v8:univ,v9:univ,v10:univ \| ((v10->v9->v8) in (B->(C->D)) and (all v11:B \| (v11.(v10->v9->v8)) in (C->D) and (all v12:C \| one(v12.(v11.(v10->v9->v8))) and (v12.(v11.(v10->v9->v8))) in D) and (all v13:D \| one((v11.(v10->v9->v8)).v13) and ((v11.(v10->v9->v8)).v13) in C)) and (all v14:univ,v15:univ \| ((v15->v14) in (C->D) and (all v16:C \| one(v16.(v15->v14)) and (v16.(v15->v14)) in D) and (all v17:D \| one((v15->v14).v17) and ((v15->v14).v17) in C)) implies (((v10->v9->v8).v14).v15) in B)) implies ((((this.f).v8).v9).v10) in A)` | the recursion composes to arbitrary depth: the innermost `one/one` on `C,D` is reached through **two** levels of plain decl-bound quantifiers (`v0:A`, `v1:B`); every column along the way is unmarked except the innermost, so **both** univ-leaf blocks (`v4,v5` and `v8,v9,v10`) are fully redundant (bare membership consequents) and mettle omits them — the lowered goal keeps only the plain-decl-bound chain down to the real `one`/`one` tests |
| L26 | n7: `f: A -> some (B one -> one C)` (double mark: outer column **and** nested arrow) | `all this:S \| (this.f) in (A->(B->C)) and (all v0:A \| some(v0.(this.f)) and (v0.(this.f)) in (B->C) and (all v1:B \| one(v1.(v0.(this.f))) and (v1.(v0.(this.f))) in C) and (all v2:C \| one((v0.(this.f)).v2) and ((v0.(this.f)).v2) in B)) and (all v3:univ,v4:univ \| ((v4->v3) in (B->C) and (all v5:B \| one(v5.(v4->v3)) and (v5.(v4->v3)) in C) and (all v6:C \| one((v4->v3).v6) and ((v4->v3).v6) in B)) implies (((this.f).v3).v4) in A)` | an outer column mark (`some`, the `rhs_mult` of the *outer* arrow) and a nested arrow's own marks **coexist and both apply**: the `all v0:A` block carries *both* the `some` mult test *and* the full recursive membership/column structure of the nested type — proving the two are independent, additive checks, not a choice between "test a multiplicity" and "recurse" |
| L27 | `sig A { f: disj set B }` (post-colon field `disj`) | `all this: this/A \| all that: this/A \| !(this = that) implies no ((this . this/A.f) & (that . this/A.f))` — emitted alongside the ordinary `(this.f) in B` domain/mult facts (DumpK2, `pd1`) | cross-atom value disjointness: distinct owner atoms map to disjoint field values. **Uniform across arity/multiplicity** — `f: disj B` (default `one`) keeps the same `no(this.f & that.f)` next to its `one(this.f)` fact (`pd_one`); `f: disj set B -> B` (arity-3) still compares the owner-joined slices `this.f`/`that.f` (arity-2), never the raw relation (`pd_arrow`). mettle: `als_core::lower::Lowerer::field_bound_disj_fact` (a `var` field ⇒ `always`-wrapped `no`, matching L15's group convention) |
| L28 | `sig A { f: disj set B }` `run { some a1, a2: A \| a1 != a2 and some (a1.f & a2.f) }` for 4 | **UNSAT**; the same model with `f: set B` (no `disj`) is **SAT** | decisive behavioral pair confirming L27's fact is exactly what forbids the overlap — the disjointness is the only difference between the two models. `run { some A }` over `f: disj set B` stays **SAT** (the fact is satisfiable, not vacuously false). Jar 6.2.0, sym 0, noOverflow true |
| L29 | `run { some x: disj B \| some x }` (post-colon `disj` on a **quantifier / run-pred param** decl) | jar **resolve error**: `Local variable "x" cannot be bound to a 'disjoint' expression.` | post-colon `disj` is legal **only on a field bound** (L27); on a quantifier / param decl the reference rejects it at resolve. mettle accepts it leniently (mt-027 over-accept class) and **defers typed** at lowering (`bound_disj_unpinned`), never synthesizing a fact for a construct the jar forbids |

Rule (jar-verified, generalizes L4): translating `r in (lhs m-> n rhs)` for any
relation-valued `r` is a function of `(r, lhs, m, n, rhs)` that emits membership
`r in (lhs_flat -> rhs_flat)` plus two columns — one iterating `lhs`'s own
tuples and checking `n`/`rhs`'s shape on the joined-from-the-left remainder,
one iterating `rhs`'s tuples checking `m`/`lhs`'s shape on the
joined-from-the-right preimage. "Checking a side's shape" means: emit a
`MultTest` if that side carries a multiplicity mark, **and** recurse the same
function if that side is itself an arrow — both apply if both are present
(L26). "Iterating a side's tuples" decl-binds one variable directly when the
side is a plain (non-arrow) relation of any arity (Kodkod decl-binds any-arity
relations with a single tuple variable); when the side is itself an arrow it
has no single named relation to bind against, so it destructures into one
fresh `univ`-bound variable per leaf (a leaf is a non-arrow operand, however
deep), guarded by the recursive membership+column check on the reconstructed
leaf-tuple (L20's `v3,v4` block, L22's `v0,v1` block, L26's outer `v3,v4`
block). A column whose "check" is empty — no mark on that side, and the other
side is not itself an arrow to recurse into — is omitted entirely (§10.3's
existing divergence (e), which generalizes cleanly to any recursion depth: a
joined slice of a value already known to lie in a flat product is trivially a
subset of the corresponding sub-product, so the redundant membership is safe
to drop at every depth, not just the top level). mettle: `als_core::lower::
Lowerer::arrow_value_constraint` (`crates/als-core/src/lower.rs`), a reusable
seam over any `RelExprId`, not hard-wired to `this.f`.

**Conjunct position (jar-verified, probes p1–p6).** The field-group `disj` fact
is emitted as a **field-level conjunct**: right after **all** of the owner sig's
per-field mult+domain facts (§2.5 item 2) and **before** the command formula
(§2.5 item 3). mettle places it in a dedicated `Provenance::FieldDisjFact(SigId)`
conjunct group between the field-facts loop and the appended-facts loop; being a
plain conjunction the exact position is verdict-neutral (semantic congruence).
The `als-types` seam is `ResolvedSig::field_disj_groups: Vec<Vec<FieldId>>`
(populated in `resolve_one_field`, source order, groups of ≥2 fields only). The
control `sig S { a, b: set E }` (no `disj`) emits **no** such conjunct (probe p7).

Rows **L27–L29** (post-colon `disj`: the `f: disj e` field fact and its DumpK2 dump, the decisive SAT/UNSAT behavioral pair, and the quant-decl resolve error) were added by **mt-040**, when the field case was jar-pinned and lowered while the quant-decl case was confirmed a jar resolve error and left an honest typed defer.

The choice-recording seam that makes this possible (mt-031 Part A,
[reference/alloy6-resolution.md](alloy6-resolution.md) §4.4) is documented in
`crates/als-types/src/choice.rs`: the mt-025 checker records, per
`(ModuleId, ExprId)`, what every name/spine resolved to (sig / field + implicit
`this` / call + overload + receiver / bound var / macro-with-nested-table), so
the lowerer replays §4.4 rather than re-deriving it. The recording is additive
and provably non-behavioral (the alloy4fun resolve gauge is **byte-identical**
before/after over all 150,891 codes).

### 10.4 mt-033 solve/encode goldens (jar-verified 2026-07-16)

Harness: `crates/als-conform/shim/OracleShim.java` driven directly (symmetry 0,
noOverflow **true** = LEDGER-001 forbid, sat4j; `enumCap 0` = verdict, `enumCap
-1` = exhaustive SB-0 count). Compared to mettle's `als_core::solve_goal` /
`als_core::enumerate` over the same hand models (`crates/als-core/tests/solve.rs`,
which pins each jar answer in a comment and never runs the jar). The gauge is
**verdict + SB-0 count only** (ADR-0002); instance tuples are never diffed.

**Verdict goldens (all mettle == jar):** quantifier-over-join SAT; acyclicity of
a non-empty total successor function UNSAT; two `in`-subset sigs disjoint SAT;
explicitly-scoped `extends` children SAT; `one`-field multiplicity SAT; `#A = 2`
SAT and `#A > 3` (scope 3) UNSAT; `check` polarity (a `some A` assertion with an
empty-A counterexample → SAT); `one`-sig field SAT; abstract-parent-equals-union
SAT; reflexive-transitive-closure reachability SAT; `lone` sig forced empty SAT;
transpose-in-join SAT; `Int`-field compared to a literal SAT; cardinality-compare
(`#A = #B`) SAT; relational override SAT.

**SB-0 enumeration counts (mettle == jar):**

| Model | jar SB-0 count | mettle | note |
|---|---|---|---|
| `run { some A } for 3` | **7** | 7 | translation-ref probe T3 (raw non-empty subsets of 3) |
| `run { #A = 2 } for 3` | **3** | 3 | the 2-subsets of 3 atoms |
| `oracle/test1.als` `show` (`run { some r } for 3`) | **1129** | 1129 | the marquee number — fields + `set` multiplicity + domain constraints, no existential |

**Skolemization count divergence (verdict matches; count does not — documented,
not a bug).** `oracle/test1.als`'s `check NoEmpty` (`all b: B | some b.r`, negated
to `some b: B | no b.r`) is **SAT** in both. Its SB-0 count is **jar 561 vs
mettle 464**: the jar's `skolemDepth 0` turns the top-level existential into a
skolem constant relation `$NoEmpty_b` and counts its assignments too (multiplying
the raw count by the number of witnesses per instance), while mettle does **not**
skolemize (ADR-0011, §2.3). This never changes the verdict — so **SB-0 count
parity holds only for goals with no skolemizable top-level existential** (`some r`
above is a multiplicity test, not `∃x`, hence 1129 matches exactly). Recorded in
LIMITATIONS.

**A genuine mt-029 scope bug surfaced — FIXED at review (probe S1, jar-verified
2026-07-16).** An **abstract** parent whose two `extends` children are *unscoped*
under a default `for 3` — `abstract sig A {} sig B extends A {} sig C extends A
{} run { some B and some C } for 3` — is **SAT** in the jar (probe: `#C = 2` is
SAT, `#B = 3 and #C = 3` is UNSAT, so each child's upper is 3 and the pair shares
the 3 atoms). mettle's per-change-restart fixpoint back-derived `C = A(3) − B(3)
= 0` via the abstract-difference rule after `B` (alone) inherited the parent
scope. **Root cause pinned from `ScopeComputer.computeScopes` at the pinned
commit: each derivation rule runs as one full pass over all sigs (changes
accumulate live within the pass), is re-run to exhaustion, then control restarts
from the top** — so `derive_scope_from_parent` scopes *both* unscoped siblings
in one sweep and the difference rule never sees a half-updated state. (Also
pinned: the childless-enum→0 assignment does **not** set the rule's changed
flag.) `scope.rs` now ports the pass-at-a-time discipline; the regression
(`abstract_unscoped_children_scope_bug` in `tests/solve.rs`, plus the scope-table
pin in `tests/scope.rs`) is live, and the 11 baseline disagreements this caused
are gone. Encoder goldens use `in`-subset sigs and explicitly-scoped children to
test subset-sig encoding cleanly.

**Encoder design (mt-033).** Bottom-up over the three-sorted IR: each `RelExpr`
→ a sparse boolean **matrix** (only upper-bound tuples stored, keyed by tuple in
lexicographic order), each `Formula` → a Tseitin `Bool` (constant or one literal),
each `IntExpr` → a two's-complement bit-vector. Variable layout is ADR-0011
decision 3: every bounded relation's `upper ∖ lower` tuples get primary variables
first, in `RelId` × tuple order, then Tseitin auxiliaries; blocking over the
primary variables only gives the raw SB-0 count. Closure is iterated squaring
(`⌈log₂|U|⌉` rounds); `lone`/`one` use pairwise at-most-one; cardinality is a
sequential ripple-carry count; `int[·]` a gated two's-complement sum with an
overflow flag conjoined as `¬flag` when overflow is forbidden. **Measured
integer needs of the 124 lowerable corpus commands: `Const` (36), `Card` (46),
`AtomToInt` (68) — zero arithmetic / `sum` / int-ITE**, so those are typed defers
(`TranslateError::LoweringUnsupported`, never a wrong verdict); the full
integer/counting fidelity is Rung 4 (ADR-0011).

**Corpus end-to-end (all 167 files, `crates/als-core/tests/solve_corpus.rs`).**
564 root-module commands, post-scope-fix at the default 1s/command budget
(`METTLE_SOLVE_BUDGET_MS` env-scales, mt-014 idiom): **440 lower-defer, 56
solved (28 SAT / 28 UNSAT), 68 over-budget** (grounding-heavy goals —
quantifiers ground without env-aware caching this rung, a non-gating perf item),
**zero panics, deterministic** (a second solve of each small command gives the
same verdict). Against the `baselines/` overlap, **one**
disagreement remains: `mediaAssets.als[3]` `check PasteNotAffectHidden`
(`mettle=SAT / jar=UNSAT`) — root-caused by mt-034 below. (The pre-fix numbers —
81 solved / 44 agree / 12 disagree at 5s — dropped 11 disagreements to the scope
fix; some previously-trivial wrong-scope commands became real problems and moved
to over-budget.)

### 10.5 mt-034 evaluator + self-check net (jar/baseline-verified 2026-07-17)

**Evaluator design.** A direct three-sorted evaluator over a concrete
`Instance` (`crates/als-core/src/eval.rs`, this §6): each `Formula` →
`bool`, `RelExpr` → `TupleSet`, `IntExpr` → `i64`. It is an **independent
second implementation** of the same semantics the mt-033 encoder emits as SAT
gates — quantifiers/comprehensions ground over their bound's concrete tuples,
closure is a concrete fixpoint, cardinality/`int[·]`/`Int[·]` read the Int-atom
range (§1.3). It handles exactly the encoder's slice (no arithmetic/`sum`/int-ITE
— same typed defer, so the two stay a **matched pair**); temporal kinds return a
typed error (never reached — lowering defers temporal). **Overflow (§2.4):** the
encoder accepts an instance iff `goal ∧ ⋀ᵢ¬overflowᵢ`; the evaluator mirrors this
as `goal_holds ∧ (allow_overflow ∨ ¬overflowed)`, tracking `#e` count overflow
(count > signed max) and `int[·]` per-step signed-add overflow. A solver-produced
instance never overflows (the solver conjoined every `¬overflowᵢ`), so the
self-check never rejects one on overflow; the path exists only so the brute-force
differential's accept-set equals the solver's.

**Encoder↔evaluator differential (the strongest net, all equal).** For a dozen+
small hand models we brute-force **every** candidate instance (each relation's
`upper∖lower` tuples on/off) and count those the evaluator accepts; the count
equals mt-033's `enumerate` SB-0 count for every model
(`tests/eval_differential.rs`): `some`/`all`/`one`/`lone`/`no`, closure &
acyclicity, `*`-closure, `in`-subset sigs, `one`/`lone` field multiplicity,
`#A=#B` and `#A=2`, override (`++`), `<:`/`:>`, transpose, comprehension,
union/intersect/diff. Two independent semantics agreeing on exact counts is the
real gauge.

**Corpus self-check (0 failures).** `solve_corpus` now re-evaluates every solved
SAT instance against its full goal in checked mode: **0 self-check failures**
across all 167 files (28 SAT solved), `mediaAssets.als[3]` included.

**mediaAssets root cause — an *under-constrained goal*, not an encoder bug.** The
lone baseline disagreement is `mediaAssets.als[3]` `check PasteNotAffectHidden`
(mettle SAT / jar UNSAT) — **not** `PasteCut`, which is `[2]` and agrees SAT/SAT;
earlier notes (including §10.4 above, now corrected) mislabeled it. The mt-034
self-check **passes** on mettle's SAT instance: the instance genuinely satisfies
mettle's own goal, which is strictly **weaker** than the jar's. The missing
constraint is the **field-group `disj`**: `sig CatalogState { disj hidden,
showing: set assets }` declares `hidden`/`showing` pairwise disjoint (`all cs |
no (cs.hidden & cs.showing)`), and combined with the appended fact
`hidden+showing = assets` it pins `cs".hidden` under `paste` (which never
mentions `hidden`), making the assertion a theorem. The `Decl` AST carries
`is_disj` (`als-syntax`) but `als_types::ResolvedField` drops it, so the lowerer
never synthesizes the disjointness. Confirmed minimally (jar-verified reasoning):
`sig E {} sig S { disj a, b: set E } assert D { all s: S | no (s.a & s.b) } check
D for 3` is a theorem (jar UNSAT) yet mettle returns **SAT** (spurious
counterexample); the `disj`-less control is SAT in both. **Fix is not contained
to `lower.rs`** — it needs an `als-types` change to record the field-group
disjointness plus a lowering conjunct.

**RESOLVED (mt-038, 2026-07-17).** `als_types::ResolvedSig` now carries
`field_disj_groups: Vec<Vec<FieldId>>` (populated in `resolve_one_field`, a pure
widening — resolve verdicts/diagnostics byte-identical), and the lowerer
synthesizes the staged `no (fi & fj)` fact per group
(`Provenance::FieldDisjFact`, §10.3 rows L15–L19, jar-pinned by probes p1–p7).
The `mediaAssets.als[3]` disagreement clears — the `check` is now UNSAT in both.
Regression pin renamed `field_disj_synthesizes_disjointness` in
`tests/solve.rs`; goldens `golden_field_disj_*` / `field_disj_var_group_defers`
in `tests/lower.rs`. `firewire.als` uses the same construct but stays behind a
higher-order-quantifier typed defer (expected).

### 10.6 mt-038 higher-order skolemization probes (jar-verified 2026-07-17)

Harness: `scratchpad/probe/DumpK2.java` (`debugExtractKInput()`, symmetry 0,
noOverflow false, `inferPartialInstance` false) over `scratchpad/probe/ho/*.als`.
The dump is the Kodkod goal **before** Kodkod's internal skolemization (the
solver log line `optimizing bounds and formula (… skolemizing)` runs *after*
`debugExtractKInput`), so it shows the quantifier with its **skolem-named
variable** (`<cmdLabel>_<var>`) and the decl-membership/multiplicity conjuncts A4
attaches, but not the free relation Kodkod mints. That free relation carries
lower `{}` and upper = the constant upper bound of the decl's bound expression,
and is named `$<cmdLabel>_<var>` in a decoded instance (probe T9). mettle mints it
directly at lowering (a real `Ir::relations` entry + `Bounds` entry) since it has
no separate Kodkod skolemization pass.

| # | Case | Jar dump (relevant conjunct) | Pinned fact |
|---|---|---|---|
| T9a | `run foo { some r: set A \| some r }` | `some foo_r: set this/A \| some foo_r` | a top-level existential over a `set`-marked unary decl skolemizes: variable `foo_r` = `<cmdLabel>_<var>`; skolem relation upper = `upper(A)`, lower `{}`; replacement = membership `$foo_r in A` (Kodkod adds it internally from the decl expr) ∧ body. `set` adds **no** multiplicity test |
| T9b | `run foo { some f: A one -> one B \| some f }` | `some foo_f: set this/A -> this/B \| foo_f in (A->B) and (all v0:A \| one(v0.foo_f) and (v0.foo_f) in B) and (all v1:B \| one(foo_f.v1) and (foo_f.v1) in A) and some f` | a mult-marked arrow decl skolemizes to a relation of the arrow's arity, upper = `upper(A)×upper(B)`; the replacement is exactly `arrow_value_constraint` (membership + per-column mults) ∧ body — the same seam the field-bound path (L4/L20–L26) uses. mettle omits the redundant per-column memberships (divergence (e)) |
| T9c | `assert Inj { all f: A lone -> B \| some f } check Inj` | `!(all Inj_f: set A -> B \| (Inj_f in (A->B) and (all v0:A \| (v0.Inj_f) in B) and (all v1:B \| lone(Inj_f.v1) and (Inj_f.v1) in A)) implies some Inj_f)` | under a `check` (outer `!`), a **universal** HO decl is skolemizable — after NNF `!all` is `∃`. The replacement is `(decl-constraint) implies body`; the enclosing `!` turns `!(⋯ ⟹ some f)` into `decl-constraint ∧ ¬(some f)` — the counterexample form. Confirms the polarity rule: an `all` at **negative** polarity is effective-existential and emits `Implies(bound_constraint(X), body)` |
| T9d | `run foo { all r: set A \| some r }` | `ERROR: edu.mit.csail.sdg.alloy4.ErrorType: Analysis cannot be performed since it requires higher-order quantification that could not be skolemized.` | a HO `all` at **positive** polarity (effective-universal) is **not** skolemizable → the jar raises `HigherOrderDeclException`, an **error**, not a verdict. mettle defers with the same message text (typed, never a wrong verdict) |
| T9e | `run foo { all x: A \| some r: set A \| x in r }` | same `ERROR` as T9d | a HO existential **nested under a universal** (`all x`) cannot be skolemized at depth 0 (would need a skolem *function*). Same error; mettle defers |
| T9f | `pred p[r: A -> B] { some r } run p` | `some p_r: set this/A -> this/B \| p_r in (A->B) and some p_r` | a run-pred **relation-valued parameter** (arity ≥ 2, default `set`) is a top-level existential → skolemized as a free relation, membership `$p_r in (A->B)` ∧ body. Variable `p_r` = `<predName>_<var>`. A plain product bound adds membership only (no per-column mults) |
| T9g | `run foo { some r: lone A \| some r }` / `some r: some A \| no r` | `some foo_r: lone this/A \| some foo_r` / `some foo_r: some this/A \| no foo_r` | `lone`/`some`-marked unary decls skolemize like `set` but add the matching multiplicity test on `$foo_r` (`lone $foo_r` / `some $foo_r`) alongside membership |

**The polarity rule (as implemented in `bind_decls_vars`/`run_pred`, mt-038).**
mettle does not NNF the goal; it threads a `SkolemPolarity { positive, blocked }`
through `lower_formula` (`positive` flips on `not`, on an `implies` antecedent, and
is set false for a `check`'s negated body before lowering; `blocked` is set by an
effective-**universal** quantifier body and by non-monotone contexts —
`iff`/int-ITE condition — and by comprehension/`sum`/temporal bodies). A HO decl
is **skolemizable** iff its quantifier is effective-existential *and* `!blocked`:
a `some` at positive polarity (emit `And([bound_constraint(X), body]`), or an
`all`/`no` at negative polarity (emit `Implies(bound_constraint(X), body)` /
`Implies(bound_constraint(X), Not(body))`; the enclosing `!` discharges it). This
is sound in a non-NNF lowering because the surrounding context down to the goal
root is a monotone Boolean context (∧/∨ only — `blocked` excludes ∀ and
non-monotone connectives) with the tracked parity, so `∃` pulls to the top past
∧/∨/∨-with-free-var without a skolem function. Everything else keeps a typed
defer aligned with the jar's `HigherOrderDeclException` text (`TranslateError::
HigherOrder`). Run-pred params are top-level (`positive`, `!blocked`) → always
skolemizable. **The skolem's upper bound** is a small sound abstract evaluation
over the lowered bound `RelExpr` against the existing `Bounds` (`abstract_upper`):
sig/field relations → their upper set, `univ`/`none`/`iden` constants, product,
union, intersect (∩ of uppers), difference (upper of lhs), override (∪ of uppers),
join (relational join of uppers), transpose, `^`/`*` closure; anything else
(a bound-variable-dependent bound, comprehension, `Int[·]`, ITE, prime) → `None` →
typed defer. First-order quantifiers are **never** skolemized (ADR-0011 unchanged);
the SB-0 "skolemization count divergence" note (§10.4) therefore still applies only
to first-order goals mettle chooses not to skolemize, and the pinned SB-0 goldens
(no HO decls) are unchanged.

### 10.7 mt-043 integer arithmetic & overflow probes (jar-verified 2026-07-18)

Harness: `scratchpad/probe/ProbeR4.java` (drives `TranslateAlloyToKodkod.
execute_command` via `A4Options`, dumps verdict + exhaustive SB-0 count + the
first instance's relation dump). Oracle: `oracle/org.alloytools.alloy.dist.jar`
(6.2.0), OpenJDK 21, `sat4j`, `symmetry=0`. Each row states `noOverflow`
explicitly (LEDGER-001). All arithmetic uses the `fun/…` operator forms via
`open util/integer`; `for 3 but 4 int` (range −8..7) unless noted.

| # | Case | noOverflow | Verdict / value |
|---|---|---|---|
| I1 | `div[-5,2]` = ? | false | **−2** (SAT); `=−3` UNSAT → **division truncates toward zero** |
| I2 | `div[5,-2]`, `div[-5,-2]` | false | **−2**, **2** → toward-zero both signs |
| I3 | `rem[-5,2]`, `rem[5,-2]` | false | **−1**, **1** → **remainder takes the sign of the dividend** (Java `%`) |
| I4 | `4 << 1`, `4 >> 1`, `(0-8) >> 1`, `(0-8) >>> 1` | false | **8**, **2**, **−4**, **4** → `<<`=logical-left, `>>`=**arithmetic** (sign-extend) right, `>>>`=**logical** (zero-fill) right |
| I5 | `plus[7,7]`, `mul[3,3]` | false | **−2**, **−7** → two's-complement wrap (14→−2, 9→−7) |
| I6 | `div[5,0]` = ? | false | **−1** (all-ones) — SAT only at −1; **jar-specific**, not 0 |
| I7 | `rem[5,0]` = ? | false | **5** — remainder-by-zero returns the **dividend** |
| I8 | `div[(0-8),(0-1)]` (MIN/−1) = ? | false | **1** — SAT only at 1; a division-algorithm artifact (the mathematically-correct 8 is out of range). Flagged: allow-mode value only; forbid excludes it |
| I9 | `plus[7,7] < 0` | false / true | **SAT** (−2<0) / **UNSAT** — the LEDGER-001 decisive test |
| I10 | `div[5,0]`, `div[(0-8),(0-1)]`, `rem[5,0]` reflexive `x=x` | true | **UNSAT** each (div-by-0, MIN/−1, rem-by-0 all set overflow); `div[5,2]=div[5,2]` **SAT** control |
| I11 | `all n: Int | plus[n,7] >= n` | false / true | **UNSAT** (breaks at n=7: 7+7 wraps) / **SAT** — **universal-position overflow rescues the ∀** (see §11.3) |
| I12 | `#A = 8` for exactly 8 A, 4 int | false / true | **SAT** (count 8 wraps to −8, `=8`≡`=−8`) / **UNSAT** — `#` cardinality participates in overflow exactly like arithmetic |
| I13 | `#A > 0` for exactly 8 A | false / true | **UNSAT** (count wraps to −8, `−8>0` false) / **UNSAT** (count overflow excluded); `#A=7` for 7 A forbid **SAT** control |

### 10.7b mt-044 LEDGER-005 residual closure probes (jar-verified 2026-07-19)

Harness: `scratchpad/probe/ProbeR4.java` (rebuilt; the mt-043 original was gone). One
JVM process, driving `TranslateAlloyToKodkod.execute_command` via `A4Options` in a
loop over in-memory models (`CompUtil.parseEverything_fromString`), sat4j,
symmetry 0, `for 3 but 4 int` throughout. Both named LEDGER-005 residuals closed
in one session (all sanity anchors reproduced first — see below).

**Critical harness finding, load-bearing for everything below:** negative integer
literals **must** be spelled `negate[k]` (`util/integer`, genuine `IMINUS`
arithmetic via `fun/sub`), **not** `(0-k)`. The raw hyphen `-` is *always*
relational set-difference between two singleton-Int atoms (`(0-5)` evaluates to
the plain atom **`0`**, not −5 — confirmed: `X.v=(0-5)` gives `v=0`). The **sole**
exception is the one documented peephole at exactly `k = bw_max+1` (=8 at bw 4):
`TranslateAlloyToKodkod`'s `ExprBinary MINUS` case specially folds `(0-8)` to the
`MIN` constant, letting the otherwise-unwritable most-negative literal be spelled
this one way. `(0-1)`, `(0-5)`, etc. are **not** covered by that peephole and
silently mean something else entirely. `negate[k]` works uniformly for every `k`
in `1..8` (confirmed: `negate[8]` also gives `-8`, agreeing with the `(0-8)`
peephole on that one value). All probes below use `negate[k]`.

**Sanity anchors — all reproduced** (OpenJDK 21, jar 6.2.0, sat4j, sym 0, allow
mode unless noted): `div[negate[5],2]=-2`, `div[5,negate[2]]=-2`,
`div[negate[5],negate[2]]=2`, `rem[negate[5],2]=-1`, `rem[5,negate[2]]=1`,
`rem[x,0]=x` (checked at x=3,-5), `div[3,0]=div[5,0]=div[7,0]=-1`,
`div[(0-8),(0-1)]=1` (reproduces **literally as spelled** — see the important
caveat below), `plus[7,7]=-2`, `mul[3,3]=-7`. No contradiction with any pinned
value — probing proceeded.

#### Residual 1 — full 16×16 `div`/`rem` sweep (allow mode)

Method: one solve per pair, `one sig X { d: one Int, r: one Int } fact { X.d =
div[a,b] and X.r = rem[a,b] } run {} for 3 but 4 int`, value read from the
`this/X<:d={X$0->N}` / `this/X<:r={X$0->N}` relation-dump lines of
`A4Solution.toString()` (never the eval API). 512 pairs total (256 divs + 256
rems packed 2-per-solve = 256 solves), ~35ms/solve.

**`div[a,b]`** (allow mode, `for 3 but 4 int`; rows = dividend `a`, cols = divisor `b`):

| a \ b | -8 | -7 | -6 | -5 | -4 | -3 | -2 | -1 | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **-8** | 1 | 1 | 1 | 1 | 2 | 2 | 4 | -8 | 1 | -8 | -4 | -2 | -2 | -1 | -1 | -1 |
| **-7** | 0 | 1 | 1 | 1 | 1 | 2 | 3 | 7 | 1 | -7 | -3 | -2 | -1 | -1 | -1 | -1 |
| **-6** | 0 | 0 | 1 | 1 | 1 | 2 | 3 | 6 | 1 | -6 | -3 | -2 | -1 | -1 | -1 | 0 |
| **-5** | 0 | 0 | 0 | 1 | 1 | 1 | 2 | 5 | 1 | -5 | -2 | -1 | -1 | -1 | 0 | 0 |
| **-4** | 0 | 0 | 0 | 0 | 1 | 1 | 2 | 4 | 1 | -4 | -2 | -1 | -1 | 0 | 0 | 0 |
| **-3** | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 3 | 1 | -3 | -1 | -1 | 0 | 0 | 0 | 0 |
| **-2** | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 2 | 1 | -2 | -1 | 0 | 0 | 0 | 0 | 0 |
| **-1** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | -1 | 0 | 0 | 0 | 0 | 0 | 0 |
| **0** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **1** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | -1 | -1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| **2** | 0 | 0 | 0 | 0 | 0 | 0 | -1 | -2 | -1 | 2 | 1 | 0 | 0 | 0 | 0 | 0 |
| **3** | 0 | 0 | 0 | 0 | 0 | -1 | -1 | -3 | -1 | 3 | 1 | 1 | 0 | 0 | 0 | 0 |
| **4** | 0 | 0 | 0 | 0 | -1 | -1 | -2 | -4 | -1 | 4 | 2 | 1 | 1 | 0 | 0 | 0 |
| **5** | 0 | 0 | 0 | -1 | -1 | -1 | -2 | -5 | -1 | 5 | 2 | 1 | 1 | 1 | 0 | 0 |
| **6** | 0 | 0 | -1 | -1 | -1 | -2 | -3 | -6 | -1 | 6 | 3 | 2 | 1 | 1 | 1 | 0 |
| **7** | 0 | -1 | -1 | -1 | -1 | -2 | -3 | -7 | -1 | 7 | 3 | 2 | 1 | 1 | 1 | 1 |

**`rem[a,b]`** (allow mode, `for 3 but 4 int`):

| a \ b | -8 | -7 | -6 | -5 | -4 | -3 | -2 | -1 | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **-8** | 0 | -1 | -2 | -3 | 0 | -2 | 0 | 0 | -8 | 0 | 0 | -2 | 0 | -3 | -2 | -1 |
| **-7** | -7 | 0 | -1 | -2 | -3 | -1 | -1 | 0 | -7 | 0 | -1 | -1 | -3 | -2 | -1 | 0 |
| **-6** | -6 | -6 | 0 | -1 | -2 | 0 | 0 | 0 | -6 | 0 | 0 | 0 | -2 | -1 | 0 | -6 |
| **-5** | -5 | -5 | -5 | 0 | -1 | -2 | -1 | 0 | -5 | 0 | -1 | -2 | -1 | 0 | -5 | -5 |
| **-4** | -4 | -4 | -4 | -4 | 0 | -1 | 0 | 0 | -4 | 0 | 0 | -1 | 0 | -4 | -4 | -4 |
| **-3** | -3 | -3 | -3 | -3 | -3 | 0 | -1 | 0 | -3 | 0 | -1 | 0 | -3 | -3 | -3 | -3 |
| **-2** | -2 | -2 | -2 | -2 | -2 | -2 | 0 | 0 | -2 | 0 | 0 | -2 | -2 | -2 | -2 | -2 |
| **-1** | -1 | -1 | -1 | -1 | -1 | -1 | -1 | 0 | -1 | 0 | -1 | -1 | -1 | -1 | -1 | -1 |
| **0** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **1** | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 0 | 1 | 1 | 1 | 1 | 1 | 1 |
| **2** | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 0 | 2 | 0 | 0 | 2 | 2 | 2 | 2 | 2 |
| **3** | 3 | 3 | 3 | 3 | 3 | 0 | 1 | 0 | 3 | 0 | 1 | 0 | 3 | 3 | 3 | 3 |
| **4** | 4 | 4 | 4 | 4 | 0 | 1 | 0 | 0 | 4 | 0 | 0 | 1 | 0 | 4 | 4 | 4 |
| **5** | 5 | 5 | 5 | 0 | 1 | 2 | 1 | 0 | 5 | 0 | 1 | 2 | 1 | 0 | 5 | 5 |
| **6** | 6 | 6 | 0 | 1 | 2 | 0 | 0 | 0 | 6 | 0 | 0 | 0 | 2 | 1 | 0 | 6 |
| **7** | 7 | 0 | 1 | 2 | 3 | 1 | 1 | 0 | 7 | 0 | 1 | 1 | 3 | 2 | 1 | 0 |

**Verified programmatically against every cell**: for every `(a,b)` with `b≠0`
**except** `(a,b)=(-8,-1)` (the MIN/−1 case, below), `div[a,b]` equals Java `a/b`
(truncating toward zero) and `rem[a,b]` equals Java `a%b` (sign of the dividend)
**exactly — zero deviating cells**. This closes the "verify the rem table is
exactly Java `%`... and div is exactly Java `/`... flag ANY cell that deviates"
requirement with a clean result: no deviation anywhere except the one
mathematically-undefined edge case.

**`div[x,0]` closed form (the residual):** reading the `b=0` column,

```
div[x,0] = -sign(x) =  1   if x < 0   (uniform for ALL negative x, including MIN=-8)
                        0   if x = 0
                       -1   if x > 0   (already pinned pre-mt-044)
```

This holds **uniformly across the entire range, with no special case at MIN** —
`div[-8,0]=1`, same as `div[-1,0]=1`. `rem[x,0]=x` (already pinned) holds
unchanged for every x including 0 and MIN. Both are simple, closed, and now
fully characterized — residual 1's open question is answered.

**Correction to the existing I8 row (important — found while confirming
`div[(0-8),(0-1)]`):** `(0-1)` is **not** a valid spelling of −1 (see the harness
finding above — it's the *set-difference peephole only applies at exactly
max+1=8*, not at 1). `div[(0-8),(0-1)]` therefore silently computes
**`div[-8,0]`** (=1, matching `div[x,0]`'s x<0 branch above), **not**
`div[MIN,-1]` as I8's label claims — the anchor "reproduces" (gives 1) only
because it's testing a different, coincidentally-matching expression. The
**correctly-spelled** `div[MIN,-1]` = `div[negate[8],negate[1]]` was probed
directly and decisively: **`div[MIN,-1] = -8`**, confirmed uniquely via
`run { div[negate[8],negate[1]] = negate[8] }` → **SAT** and
`run { div[negate[8],negate[1]] = 1 }` → **UNSAT**. This is the standard
two's-complement division-overflow wraparound (`wrap(-MIN) = wrap(8) = -8`,
the same INT_MIN/−1 overflow behavior as Java/C/x86 `IDIV`), not the "1" I8
currently states. §11.2 is updated below to carry the corrected value; I8's
row text itself is left as-is per this session's edit scope (append-only to
§10.7's table), but readers should treat I8's "1" as `div[MIN,0]`, and use
`div[MIN,-1]=-8` from here on.

**Confirmation probes** (decisive paired `run { EXPR = v } ` SAT / `run { EXPR =
v' }` UNSAT, `v'≠v`), sample of 12 pairs covering div-by-zero at positive/zero/
negative dividends, `div[MIN,-1]`, `rem[x,0]` rows, and ordinary pairs — **all
12 decisive pairs matched (12/12)**:

| Pair | `div[a,b]` | `rem[a,b]` | div decisive | rem decisive |
|---|---|---|---|---|
| div-by-zero, positive dividend (5,0) | -1 | 5 | SAT@-1 / UNSAT@0 | SAT@5 / UNSAT@6 |
| div-by-zero, zero dividend (0,0) | 0 | 0 | SAT@0 / UNSAT@1 | SAT@0 / UNSAT@1 |
| div-by-zero, negative dividend (-5,0) | 1 | -5 | SAT@1 / UNSAT@2 | SAT@-5 / UNSAT@-4 |
| div-by-zero, MIN dividend (-8,0) | 1 | -8 | SAT@1 / UNSAT@2 | SAT@-8 / UNSAT@-7 |
| `div[MIN,-1]` (-8,-1) | -8 | 0 | SAT@-8 / UNSAT@-7 | SAT@0 / UNSAT@1 |
| rem-by-zero, positive (3,0) | -1 | 3 | — | SAT@3 / UNSAT@4 |
| rem-by-zero, negative (-3,0) | 1 | -3 | — | SAT@-3 / UNSAT@-2 |
| rem-by-zero, MIN (-8,0) | 1 | -8 | — | SAT@-8 / UNSAT@-7 |
| ordinary (3,2) | 1 | 1 | SAT@1 / UNSAT@2 | SAT@1 / UNSAT@2 |
| ordinary (-6,4) | -1 | -2 | SAT@-1 / UNSAT@0 | SAT@-2 / UNSAT@-1 |
| ordinary (7,-3) | -2 | 1 | SAT@-2 / UNSAT@-1 | SAT@1 / UNSAT@2 |
| ordinary (-7,-2) | 3 | -1 | SAT@3 / UNSAT@0 | SAT@-1 / UNSAT@0 |

**Residual 1: closed.** Full sweep + closed form + 12/12 decisive confirmations,
plus a corrected `div[MIN,-1]` value with jar-verified evidence.

#### Residual 2 — deep mixed-polarity forbid-mode coverage

15 probes designed to exercise ∀∃/∃∀ nesting (inner/outer/both operands
overflowing), negation layers (`not`, `implies` antecedent, `check`), double
negation, `sum`/int-ITE under a quantifier, and mixed-classification atoms (two
operands of one comparison classifying differently) — see
`scratchpad/probe/polarity_model.py` for the executable derivation model (encodes
§11.3's rule literally, brute-enumerated over the bw4 domain) used to fix every
prediction **before** running the jar. **12/15 matched prediction; 3 genuine
mismatches, all sharing one root pattern** (below) — reported verbatim per the
"mismatch is a finding" instruction.

| # | Model sketch | Predicted forbid (derivation) | Allow | Forbid | Agree? |
|---|---|---|---|---|---|
| P1 | `plus[7,7] < 0` (control = I9) | UNSAT (exist/constant, positive polarity → `AND ¬of`) | SAT | UNSAT | ✅ |
| P2 | `all n:Int\|plus[n,7]>=n` (control = I11) | SAT (univ, positive → `OR of` rescues) | UNSAT | SAT | ✅ |
| P3 | `all n:{-8..-2}\|some m:{1..7}\|plus[m,7]=n` — (a) inner-var(exist) overflow, ∀∃ | UNSAT (m exist-classified, always overflows in domain → excluded for every n) | SAT | **SAT** | ❌ |
| P4 | `all n:{1..7}\|some m:{0}\|plus[n,7]=m` — (a) outer-var(univ) overflow, ∀∃ | SAT (n univ-classified, always overflows → rescues every n) | UNSAT | **UNSAT** | ❌ |
| P5 | `some n:{1..7}\|all m:{0}\|plus[n,7]=negate[5]` — (a) outer-var(exist, wraps a vacuous inner ∀), ∃∀ | UNSAT (n exist-classified regardless of nesting → excluded) | SAT | UNSAT | ✅ |
| P6 | `some n:{0}\|all m:{1..7}\|plus[m,7]>=0` — (a) inner-var(univ) overflow, ∃∀ | SAT (m univ-classified, always overflows → rescues) | UNSAT | **UNSAT** | ❌ |
| P7 | `not (all n:Int\|plus[n,7]>=n)` — (b) negation | UNSAT (surface `all` at negative polarity ≈ effective ∃, swapped rule) | SAT | UNSAT | ✅ |
| P8 | `not not (all n:Int\|plus[n,7]>=n)` — (c) double negation | SAT (polarity restored) | UNSAT | SAT | ✅ |
| P9 | `all n:{1..7}\|(plus[n,7]<0 implies (1=0))` — (b) implies antecedent | SAT (n univ but atom at flipped/negative local polarity → `AND ¬of`, antecedent forced false, implication vacuous) | UNSAT | SAT | ✅ |
| P10 | `assert a{all n:Int\|plus[n,7]>=n} check a` — (b) check | UNSAT (translator's own negation, same as P7) | SAT | UNSAT | ✅ |
| P11 | `some x:{1}\|(sum y:{6,7}\|plus[y,x])>negate[2]` — (d) sum under ∃ | UNSAT (x exist-classified, sum's inherited overflow excluded) | SAT | UNSAT | ✅ |
| P12 | `all n:{1..7}\|(n>0=>plus[n,7] else 0)>=0` — (d) int ITE under ∀ | SAT (n univ, then-branch overflow rescues) | UNSAT | SAT | ✅ |
| P13a | `all n:{1..7}\|some m:{±3,±5}\|plus[n,7]=mul[m,m]` — (e) mixed: univ LHS + exist RHS, both overflow | ambiguous by hand (two composition-order readings: SAT if univ-rescue dominates, UNSAT if guards fold sequentially) | UNSAT | **UNSAT** | N/A* |
| P13b | same content, operands swapped (`mul[m,m]=plus[n,7]`) — order-symmetry check | same ambiguity | UNSAT | **UNSAT** | N/A* |
| P14 | `not (some n:Int\|not (plus[n,7]>=n))` — De Morgan rewrite of I11 via `some`+`not` | SAT (surface `some` under negation ≈ effective ∀) | UNSAT | SAT | ✅ |

\* P13a/b turned out to be instances of the *same* root pattern as P3/P4/P6 (below), not a resolution of the composition-order question — the guard didn't fire at all in either ordering (forbid = allow in both), so the intended order-dependence test never got to run.

**The finding: forbid-mode's overflow guard reliably fires for single-quantifier
formulas (with or without negation/`implies`/`check` wrapping, and for `sum`
under a lone `∃`) and for *same-type* doubly-nested quantifiers (`∀∀`, `∃∃`),
but was observed to silently not fire — forbid indistinguishable from allow —
for `∀∃`/`∃∀` (mixed-type) doubly-nested quantifiers whenever the inner
quantifier's bound variable is actually used in the guarded comparison.**
Confirmed with 18 additional targeted diagnostic jar runs beyond the 15-probe
batch (`scratchpad/probe/Diag1.java`–`Diag7.java`):

- A **bare** existential exclusion works standalone: `some m:{1..7}|plus[m,7]=
  negate[8]` → forbid UNSAT (matches prediction) — isolates that exist-exclusion
  is fine *without* an enclosing quantifier.
- Wrapping the *same* exclusion inside an outer `all n:{-8..-2}| ... = n` (P3)
  flips it to SAT — guard silently inactive — **even though** the outer `n` is a
  bare variable with no arithmetic of its own (its own `accumOverflow` is the
  constant `FALSE`, so per `kodkod.engine.bool.DefCond.ensureDef` it should be a
  no-op regardless of classification).
- **Same-type nesting is robust**: `some n:{-8..-2}|some m:{1..7}|plus[m,7]=n`
  → forbid UNSAT (exclusion fires correctly); `all n:{-8..-2}|all m:{1..7}|
  plus[m,7]=n` → forbid SAT (rescue fires correctly). Both confirmed directly.
- **Vacuous inner quantifiers behave inconsistently by wrapper type**: P5's
  vacuous inner `all m:{0}` (body ignores m) still lets the outer exclusion
  fire; the mirror case with a vacuous inner `some m:{0}` under an outer `all`
  does **not** let the outer rescue fire (`all n:{1..7}|some m:{0}|plus[n,7]>=0`
  → forbid UNSAT, not the predicted SAT) — so it is not simply "vacuous inner
  quantifiers get optimized away."
- Read against the actual `kodkod.engine.bool.DefCond` source (fetched
  separately, not part of the shipped jar's `.java`): `isUnivQuant` walks the
  **Kodkod-level environment chain** looking for the innermost Int-typed binding
  whose `Decl`'s variable is in the operand's recorded `vars()`, and
  `isInt(type)` tests literal string equality against `"ints"` — a check that
  looks brittle against comprehension-restricted domains (`{x:Int|...}`, used
  throughout these probes) rather than the bare `Int` sig. This is a plausible
  *contributing* mechanism but does not by itself explain why same-type nesting
  with the identical comprehension-domain style still classifies correctly
  while mixed-type nesting does not — the precise trigger inside
  `TranslateAlloyToKodkod`'s quantifier translation (`visit_qt`) is not fully
  pinned by these probes and would need bytecode-level tracing to close
  completely.

**Residual 2: closed as "coverage" (15 probes across every requested corner,
12/15 matched prediction) but with a real, jar-verified, previously-undocumented
gap surfaced**: forbid-mode overflow guarding is unreliable specifically for
mixed-type (`∀∃`/`∃∀`) doubly-nested quantifiers where the inner variable is
non-vacuously used — a materially different (and narrower, more actionable)
characterization than "coverage still open." This refines rather than merely
extends §11.3's rule and should inform mt-044's implementation: mettle's own
guard should not silently degrade in this configuration, so this is worth a
dedicated differential test once mt-044 lands, not just a documentation note.


| I14 | `min = (0-8)`, `max = 7` | SAT — `util/integer` `min`/`max` are `min(bw)`/`max(bw)`. **Source:** `TranslateAlloyToKodkod.visit(ExprConstant)` maps `MIN`/`MAX` to `IntConstant.constant(min/max)`, i.e. **plain int constants**, not the `Int/min`/`Int/max` relations |
| I15 | `3.next = 4`, `3.prev = 2`, `7.next = 7`, `(0-8).prev = (0-8)` | first two SAT, last two **UNSAT** — `next`/`prev` are the `Int/next` binary relation and its transpose; `7.next`/`(−8).prev` are empty (chain endpoints), so the equalities with a non-empty side fail |

### 10.7c mt-044 mixed-nesting forbid-mode trigger, pinned (jar-verified 2026-07-19)

**Mission:** pin, at source level where possible and by decisive empirical
matrix where not, the exact trigger of §10.7b's residual — forbid mode's
overflow guard silently not firing (forbid ≡ allow) for some mixed-type
doubly-nested quantifiers. Sources: `DefCond`, `Skolemizer`,
`FOL2BoolTranslator`, `Environment`, `FOL2BoolCache`, `NestedSet`, `Int`/
`TwosComplementInt` (all `kodkod.engine.bool`/`kodkod.engine.fol2sat`), and
`TranslateAlloyToKodkod` — fetched from `github.com/AlloyTools/org.alloytools.alloy`
at the pinned commit **`794226dd`** (the shipped jar's own `.class` files under
`oracle/extracted_full/` are decompiled-signature-only; full `.java` sources
for these classes live in the sibling `org.alloytools.pardinus.core` module,
not `org.alloytools.alloy.core`, which is why they weren't on disk — fetched
this session into `scratchpad/src794/`, gitignored). Harness: eight new probe
files, `scratchpad/probe/ProbeSkolem{,2,3,4,5,6,7,8}.java` (gitignored,
one JVM per file, `A4Options`/`TranslateAlloyToKodkod.execute_command`, sat4j,
symmetry 0, `for 3 but 4 int`, both `noOverflow` settings per row).

#### Primary hypothesis (skolemization) — tested and refuted

The tech lead's primary hypothesis was: Kodkod skolemizes existentials up to
`A4Options.skolemDepth`; an inner `∃` under an outer `∀` skolemizes into a
skolem *function* of the outer variable once depth ≥ 1, and if the overflow
classifier's univ/exist walk runs after skolemization, the skolemized-away
existential's variable dependency could get silently reattributed to the
*outer* variable via the skolem join, flipping the classification.

Two source facts already complicate this before any run: **(a)**
`A4Options.skolemDepth` defaults to **`0`**, not some larger value (confirmed:
`new A4Options().skolemDepth == 0`, `edu.mit.csail.sdg.translator.A4Options`
line 69). **(b)** `Skolemizer.visit(QuantifiedFormula)` only skolemizes a
non-top-level quantifier when `skolemDepth >= nonSkolems.size() + newDecls.size()`
holds for every *enclosing non-skolemizable* quantifier on the path to it; for
`all n | some m | …` at the default depth 0, the outer `all` immediately fails
`0 >= 0+1`, forcing `skolemDepth = -1` for everything under it — so **the inner
`some m` is never skolemized in the default configuration**: it survives as a
genuine, separate `QuantifiedFormula(SOME)` node, with its own environment
frame, exactly like the outer `all`. The skolemization story literally cannot
be the depth-0 mechanism because no skolemization of the inner existential
happens at depth 0 in the first place.

**Decisive experiment:** swept `A4Options.skolemDepth` ∈ {0,1,2,3,4,−1} (−1
disables skolemization everywhere, even for top-level bare existentials) over
the single-quantifier controls (I9, I11, bare-∃), the same-type nested
controls (`∃∃`, `∀∀`), and P3/P4/P6 (the three mixed-nesting probes with
observed anomalies). Every row was **byte-for-byte identical across all six
depths**:

| Probe | allow | forbid @ depth 0,1,2,3,4,−1 (all identical) |
|---|---|---|
| I9 `plus[7,7]<0` | SAT | UNSAT (every depth) |
| I11 `all n:Int\|plus[n,7]>=n` | UNSAT | SAT (every depth) |
| bare-∃ `some m:{1..7}\|plus[m,7]=−8` | SAT | UNSAT (every depth) |
| `∃∃` same-type `plus[m,7]=n` | SAT | UNSAT (every depth) |
| `∀∀` same-type `plus[m,7]=n` | UNSAT | SAT (every depth) |
| **P3** `∀∃` inner-exist-drives | SAT | **SAT (every depth — anomaly present at −1 too)** |
| **P4** `∀∃` outer-univ-drives | UNSAT | **UNSAT (every depth — anomaly present at −1 too)** |
| **P6** `∃∀` inner-univ-drives | UNSAT | **UNSAT (every depth — anomaly present at −1 too)** |

Depth **−1** (skolemization off *everywhere*, including top-level bare
existentials which normally skolemize to constants regardless of depth) still
reproduces every anomaly identically. **skolemDepth is conclusively ruled out
as the trigger** — this refutes the primary hypothesis stated in the mission.
(`scratchpad/probe/ProbeSkolem.java`.)

> **Correction (round 3, 2026-07-19):** the P3/`∀∀`/`∃∃` *row values* in the
> table above were later found to be confounded by the `negate[8]` domain
> issue documented in full below — the qualitative conclusion of this
> subsection ("skolemDepth doesn't change the behavior") is unaffected (the
> confound is a translation-time overflow-guard artifact, wholly unrelated to
> Kodkod's skolemization option, so it reproduces identically at every depth
> too), but the specific SAT/UNSAT values shown for those three rows do not
> reflect the jar's true behavior on a *correctly* restricted domain. See the
> retraction below for the corrected values.

#### What the trigger actually is: ONE defect, not two — "Defect B" retracted (round 3, 2026-07-19)

With skolemization off the table, the actual mechanism was isolated
empirically by systematically varying one structural axis at a time (domain
expression style, nesting order, nesting depth, comparison operator,
arithmetic operator) and jar-verifying every cell. Read against
`kodkod.engine.bool.DefCond.ensureDef`/`isUnivQuant` (quoted in full at
§11.3): the classifier walks the **live, post-skolemization
`Environment<BooleanMatrix,Expression>` chain** (built by
`FOL2BoolTranslator.all()`/`some()`, one frame per surviving quantifier, order
innermost→outermost) looking for the *first* frame whose declared domain
`isInt()`s (a **literal string-equality check against `"ints"`**,
`DefCond.isInt`, flagged as suspicious in §10.7b) **and** whose bound variable
is in the overflowing operand's recorded `vars()`; if it finds one, the
classification is that frame's `Quantifier.ALL`/`SOME` tag; if a frame's
domain fails `isInt()`, the frame is skipped **entirely** (its variable is
never even checked) and the search continues outward; if the chain is
exhausted, the default is **existential**.

**Defect A — domain-comprehension breaks `isInt`, silently defaulting to
existential.** `Expression.INTS` (Kodkod's literal `Int` builtin) is the only
expression `isInt()` recognizes. **Any** restricted-domain expression — even
the trivial singleton `{x:Int|x=0}` — is a genuine Kodkod `Comprehension`
object whose `toString()` is not `"ints"`, so `isInt()` is false on that
frame, and the search skips straight past the variable it was looking for.
Since the fallback-when-nothing-matches is *existential*, this defect is
**invisible whenever the affected variable is genuinely existential**
(coincides with the fallback) but **wrongly excludes instead of rescuing
whenever the affected variable is genuinely universal** — exactly P4 (outer
`∀`, own domain a comprehension) and P6 (inner `∀`, own domain a
comprehension). Decisive isolation (`scratchpad/probe/ProbeSkolem2.java`,
holding the *other* variable's domain fixed and switching only the
**overflow-driving** variable's own domain from comprehension to literal
`Int` with the restricting guard moved into the body via `implies`/`and`):

| Probe | overflow-driver's domain | other var's domain | forbid | verdict |
|---|---|---|---|---|
| P4-orig | comprehension | comprehension | UNSAT | broken (predicted SAT) |
| P4, driver→bare `Int` | **bare Int** | comprehension | **SAT** | **fixed** |
| P4, other→bare `Int` | comprehension | bare Int | UNSAT | still broken |
| P6-orig | comprehension | comprehension | UNSAT | broken (predicted SAT) |
| P6, driver→bare `Int` | **bare Int** | comprehension | **SAT** | **fixed** |
| P6, other→bare `Int` | comprehension | bare Int | UNSAT | still broken |

Only the **overflow-driving variable's own** domain style matters; the other
variable's domain style is irrelevant. This is a clean, fully-deconfounded
result (4 cells × 2 probes, both directions), and — critically, established
by the round-3 audit below — **none of these six probes used `negate[8]`
anywhere**, so Defect A stands exactly as first characterized, unaffected by
the retraction that follows.

**"Defect B" (retracted): there is no nesting-position defect.** The first
pass of this investigation additionally reported a second, independent
defect — an existential nested inside a "range"-guarded (`x>=A and x<=B`)
enclosing universal supposedly disabled the guard outright, regardless of the
inner variable's own domain style, fixed by rephrasing the outer restriction
as a disjunction of equalities instead. **A round-3 tech-lead-requested audit
(triggered by an unrelated shift-semantics investigation surfacing that
`negate[8]` itself carries a permanent overflow flag — see the negate[8] note
in §10.7d below) found every one of "Defect B"'s decisive probes used
`negate[8]` as the enclosing universal's own lower domain bound
(`x>=negate[8] and x<=negate[2]`), and that this is fatal**: `negate[8]`
(`=minus[0,8]`, itself an overflowing computation) carries `accumOverflow=TRUE`
unconditionally; as a bare constant its `vars()` is empty, so it always
classifies existential (per §11.3's own text — constants are existential by
definition) and at positive polarity gets `AND ¬of`, which — because its own
`of` is `TRUE` — **forces the comparison `x>=negate[8]` to `FALSE` for every
candidate `x`, unconditionally, regardless of `x`'s real value.** A
conjunction domain `{x:Int|x>=negate[8] and x<=negate[2]}` therefore has
**zero members** in forbid mode (confirmed directly: `#{x:Int|x>=negate[8]
and x<=negate[2]}=0` is forbid-**SAT**, i.e. the domain's own cardinality *is*
0), making every `all n:{that domain}|BODY` **vacuously SAT** and every
`some n:{that domain}|BODY` **vacuously UNSAT** — independent of whatever
`BODY`'s own overflow guard does. A disjunction domain
(`x=negate[8] or x=negate[7] or …`) only loses the *one* poisoned disjunct
(still 6 of 7 members survive, confirmed: `#{...}=7` is forbid-**UNSAT** with
`negate[8]`, `#{...}=7` is forbid-**SAT** once cleaned — meaning the
`negate[8]`-spelled OR-domain was quietly missing an atom too, just not
*all* of them), so it stays non-vacuous and its "correct" behavior was never
actually about disjunction-vs-conjunction — it was **always** about the
inner existential correctly falling back to existential under Defect A
(genuinely existential ⇒ fallback is invisible), same as the AND cell would
show once cleaned.

**Decisive re-audit, clean spelling `(0-8)` (the peephole-folded MIN literal,
confirmed overflow-free below) substituted for every `negate[8]` domain
bound** (`scratchpad/probe/ProbeReaudit.java`, `ProbeReaudit2.java`):

| Cell | Original (`negate[8]`) forbid | Clean (`(0-8)`) forbid | Conclusion |
|---|---|---|---|
| P3 (`∀`-range, `∃`-range) | **SAT** ("Defect B present") | **UNSAT** | **flips — no anomaly, Defect A alone (m falls back to exist, correctly) explains it** |
| `n`=range,`m`=enum | SAT | **UNSAT** | flips |
| `n`=enum,`m`=range | UNSAT | UNSAT | unchanged (was never vacuous — only 1 of 7 disjuncts poisoned) |
| `n`=enum,`m`=enum | UNSAT | UNSAT | unchanged |
| All 6 comparison operators (=,≠,<,≤,>,≥) on the range/range cell | SAT (5 of 6) | **UNSAT** (all 6) | flips |
| NP3 (3-level, vacuous extra `∀`) | SAT | **UNSAT** | flips |
| NP4 (NP3 + inner bare `Int`) | SAT | **UNSAT** | flips |
| GAP1c (bare-Int outer, range via `implies`) | SAT | **UNSAT** | flips |
| all-all (same-type `∀∀`) | SAT | **UNSAT** | flips (see rule-2 correction below) |
| some-some (same-type `∃∃`) | UNSAT | UNSAT | unchanged |
| GAP2d (sig-`∀` outer, properly forced nonempty this round) | SAT | UNSAT (**both** spellings, once `P` is properly forced nonempty rather than left free to default empty) | flips/retracted — see §10.7d |

**Every single "Defect B" cell that showed the anomaly flips to the
naive-rule-matching UNSAT once `negate[8]` is replaced with a clean MIN
spelling.** There is no nesting-position defect. **"Defect B" is retracted
in full.** The uniform, corrected explanation for every one of these cells is
Defect A alone: whichever quantifier in the shape has a comprehension (or
sig) domain gets its classification defaulted to existential — invisible
when that variable is genuinely existential (P3's `m`, the same-type
`∃∃`'s both variables), wrong when it's genuinely universal (the same-type
`∀∀` case's `m`, which the original, confounded "all-all is robust" claim
never actually tested cleanly — see the rule-2 correction below).

**This also means "Defect A" was never actually confined to mixed-type
nesting.** It is a **per-variable** classification rule with **no dependence
on nesting shape at all**: any quantified variable whose own domain isn't
literally bare `Int`/`seq/Int` gets defaulted to existential, full stop,
whether it sits alone, doubly-nested same-type, or doubly-nested mixed-type,
and whether the enclosing/sibling quantifier(s) are bare-`Int`, comprehension,
or `sig`-typed. Confirmed with both quantifiers forced to genuinely bare
`Int` (no comprehension, no `negate[8]`, restriction via `implies`/`and` in
the body): `all n:Int|(range)implies(all m:Int|(range)implies plus[m,7]=n)`
→ forbid **SAT** (correct rescue, `m` classifies directly as universal since
its own domain is now literally `Int`) and the `∃∃` mirror → forbid **UNSAT**
(correct exclusion) — i.e. same-type nesting genuinely *is* robust, but only
once every level's domain is actually bare `Int`; the original §10.7b claim
tested it with comprehension domains and (before this audit) attributed the
coincidentally-matching UNSAT of the `∃∃` cell to "robustness" while never
noticing the `∀∀` cell's SAT was equally coincidental (propped up by the
`negate[8]` vacuous-domain artifact, not genuine rescue).

#### Open, not closed by this investigation: ITE/`implies` interaction with Defect A

Defect A's "own domain must be bare `Int`" precondition, tested on a **single**
universally-quantified variable with **no second quantifier at all**, gives
inconsistent results depending on what wraps the comparison:

| Shape (single `∀`, comprehension domain `{x:Int|x>=1 and x<=7}`, `n` is the sole/overflow-driving var) | forbid | Defect A fires? |
|---|---|---|
| Direct: `plus[n,7] >= 0` | UNSAT (predicted SAT) | **yes** |
| Under `implies` antecedent: `plus[n,7]<0 implies (1=0)` (= P9) | SAT (matches predicted) | **no** |
| Under an int-ITE: `(n>0 => plus[n,7] else 0) >= 0` (= P12) | SAT (matches predicted) | **no** |

`scratchpad/probe/ProbeSkolem8.java`. Attempts to explain this from source
(does `implies` genuinely flip `Environment.negate()`? does an ITE's
condition-formula "pre-visit" `n` in a way that changes a later lookup?)
produced multiple self-contradictory derivations — confirmed by source read
that `FOL2BoolTranslator.visit(BinaryFormula)` never calls `env.negate()` for
`IMPLIES` (only `visit(NotFormula)` does), which by itself predicts P9 should
misbehave the same way the direct-comparison row does, yet it doesn't. This
is **not closed**: whether an ITE or an `implies`-antecedent around the *same*
Defect-A-triggering shape reliably avoids the defect, sometimes avoids it, or
was coincidental in these two instances, is unknown. **Recommendation:**
mettle should treat this sub-corner conservatively (typed-defer, below), not
assume the ITE/`implies` escape generalizes.

#### Retrodiction over §10.7b's P1–P14 (100% match, corrected for the Defect-B retraction)

| # | Shape | Defect(s) applicable | Predicted (this rule) | Observed (clean re-verification) | Match |
|---|---|---|---|---|---|
| P1 | ground constants, no quantifier | none | UNSAT | UNSAT | ✅ |
| P2 | single `∀`, bare `Int` | none (bare Int, direct match) | SAT | SAT | ✅ |
| P3 | `∀`(range)`∃`(range), inner drives | **A only** (`m` falls back to existential, which is correct — `m` genuinely is `∃`) | UNSAT (guard correctly excludes) | **UNSAT once the domain's `negate[8]` bound is replaced with clean `(0-8)`** — the original `negate[8]`-spelled probe showed SAT, which was a vacuous-domain artifact, not the jar's real answer | ✅ (corrected) |
| P4 | `∀`(comprehension, drives)`∃`(trivial) | **A** | UNSAT (misclassified exist) | UNSAT | ✅ (no `negate[8]` in this probe; unaffected by the retraction) |
| P5 | `∃`(comprehension, drives, outermost)`∀`(vacuous) | A's fallback coincides (var genuinely exist) | UNSAT | UNSAT | ✅ (uses `negate[5]`, not `negate[8]`; unaffected) |
| P6 | `∃`(trivial)`∀`(comprehension, drives, inner) | **A** | UNSAT (misclassified exist) | UNSAT | ✅ (no `negate[8]`; unaffected) |
| P7 | `not(∀,\ bare\ Int)` | none (bare Int) | UNSAT | UNSAT | ✅ |
| P8 | double negation, bare `Int` | none | SAT | SAT | ✅ |
| P9 | single `∀`(comprehension) under `implies` antecedent | A's precondition met but **not observed to fire** — Open note | SAT (matches naive; mechanism open) | SAT | ✅ (retrodicted; not explained — uses range `1..7`, no `negate[8]`, unaffected by the retraction) |
| P10 | `check` (own negation), bare `Int` | none | UNSAT | UNSAT | ✅ |
| P11 | `sum` under a single `∃` | none (x genuinely exist; fallback coincides) | UNSAT | UNSAT | ✅ |
| P12 | int-ITE under single `∀`(comprehension) | A's precondition met but **not observed to fire** — Open note | SAT (matches naive; mechanism open) | SAT | ✅ (retrodicted; not explained — no `negate[8]`, unaffected) |
| P13a/b | one comparison, both operands overflow, mixed classification | out of scope (independent "composition order" question, untouched by this session) | ambiguous (as originally reported) | UNSAT (both) | N/A, unchanged |
| P14 | De Morgan rewrite of I11 via `some`+`not` | none (bare Int) | SAT | SAT | ✅ |

**12/12 in-scope probes retrodict cleanly under the single-defect (Defect A
only) rule** (P13a/b explicitly out of scope, carried over unchanged from
§10.7b). P3 is the one entry whose *documented* verdict changed in this
round — from an apparent anomaly to a clean retrodiction — once its
domain's `negate[8]` confound was removed; P4/P5/P6/P9/P11/P12 were already
clean (no `negate[8]` in any of their spellings) and are unaffected.

#### New decisive probes: what survives the Defect-B retraction

Of the six "new decisive probes" from the first pass of this section, two
(NP1, NP2 — the Defect-A depth-extension probes) used **no `negate[8]`** and
stand exactly as reported: both showed the naive rule wrong and this rule
(Defect A applying regardless of nesting depth) right. The other four
(NP3, NP4, and the two probes drawn from the AND/OR domain-shape matrix) all
depended on a `negate[8]`-spelled domain bound and their reported "Defect B"
verdicts do **not** survive — see the retraction above; re-verified, all four
now retrodict as clean Defect-A cases (correct exclusion, matching naive),
not counterexamples to naive at all.

| # | Shape | Naive predicts | This rule (Defect A only) predicts | Observed | Winner |
|---|---|---|---|---|---|
| NP1 | `∀`(range, drives)`∃`(trivial)`∃`(trivial) — Defect A through 2 extra vacuous layers | SAT | UNSAT | **UNSAT** | this rule (stands, no `negate[8]`) |
| NP2 | `∃`(trivial)`∃`(trivial)`∀`(range, drives) — Defect A, mirrored | SAT | UNSAT | **UNSAT** | this rule (stands, no `negate[8]`) |
| NP3 (corrected) | `∀`(range)`∀`(vacuous)`∃`(range, drives), clean `(0-8)` domain bound | UNSAT | UNSAT | **UNSAT** | naive (originally reported SAT via the `negate[8]` artifact — retracted) |
| NP4 (corrected) | NP3 + inner `∃`'s own domain switched to bare `Int`, clean bound | UNSAT | UNSAT | **UNSAT** | naive (originally reported SAT — retracted) |

Two fresh, genuinely decisive Defect-A probes replace the retracted
domain-shape-matrix pair (P4-m-bareInt-only, isolating that only the
overflow-driver's own domain matters, was already reported correctly in the
first pass and needs no correction):

| # | Shape | Naive predicts | This rule predicts | Observed | Winner |
|---|---|---|---|---|---|
| NP5 | P4 shape, only the **trivial** (non-driving) variable switched to bare `Int`, driving variable left as comprehension | SAT | UNSAT | **UNSAT** | this rule |
| NP6 | Sig-domained single-quantifier Defect A (see GAP2a below) — `all p:P\|plus[#p.f,7]>=0`, forced non-vacuous | SAT | UNSAT | **UNSAT** | this rule |

(`scratchpad/probe/ProbeSkolem2.java`, `ProbeSkolem3.java`,
`ProbeReaudit2.java`, `ProbeGap.java`.)

#### Gap-closing round (tech-lead review, jar-verified 2026-07-19, corrected for the Defect-B retraction)

Tech-lead review of the first pass flagged two coverage gaps that had to be
probed shut before the rule could be treated as implementable. Both use the
same harness/methodology (predictions recorded before running; sat4j,
symmetry 0, `for 3 but 4 int`, both `noOverflow` settings; decisive
allow/forbid divergence per probe) — `scratchpad/probe/ProbeGap.java`. GAP 1's
findings are **corrected** below for the Defect-B retraction; GAP 2's core
finding (sig-domain misclassification) is **unaffected** — none of GAP 2's
decisive cells (2a/2b) used `negate[8]`, and 2c/2d are addressed below.

**GAP 1 — mixed-type nesting with BOTH domains literal bare `Int`.**

| # | Shape | Predicted (naive) | allow | forbid | Result |
|---|---|---|---|---|---|
| GAP1a | `all n:Int\|some m:Int\|plus[m,7]=n` — **no restriction anywhere**, either domain or body | UNSAT | SAT | **UNSAT** | naive confirmed — guard fires correctly (no `negate[8]`, unaffected by the retraction) |
| GAP1b | `some n:{0}\|all m:Int\|plus[m,7]>=m` — univ driver (`m`) bare `Int`, `∃∀` shape (rule check) | SAT (rescue) | UNSAT | **SAT** | rule confirmed (no `negate[8]`, unaffected) |
| GAP1c (corrected) | same shape, clean `(0-8)` bound instead of `negate[8]` | UNSAT | SAT | **UNSAT** | naive confirmed — the originally-reported SAT was the vacuous-implication artifact (the antecedent `n>=negate[8]` was forced false for every `n`, making the whole `implies` vacuously true; retracted) |

GAP1a and GAP1b were always clean (no `negate[8]` anywhere in either) and
stand exactly as first reported: a fully unrestricted, or a bare-`Int`
`∃∀`-shaped, quantifier pair behaves per the naive rule, because every
variable's own domain is literally `Int` and classifies directly and
correctly. GAP1c's original "Defect B persists" verdict does **not**
survive — corrected above.

**GAP 2 — overflow-driving variable bound over a SIG domain.** `DefCond.isInt`
recognizes only the literal `Expression.INTS` builtin; a `sig` domain is
exactly as unrecognized as a comprehension. This is Defect A's general form,
**not** a new "Defect B extends to sig" finding (that framing is retracted
along with Defect B) — Defect A alone explains every GAP 2 cell.

| # | Shape | allow (established by hand) | Predicted: naive rule | Predicted: Defect A | forbid | Result |
|---|---|---|---|---|---|---|
| GAP2a | `sig P{f:set P}`; force `some p.f`; require `all p:P\|plus[#p.f,7]>=0` | UNSAT (unconditional — whichever `p` has nonempty `f` fails the raw wrapped comparison) | SAT (rescue) | UNSAT (exclude) | **UNSAT** | **Defect A confirmed for sig domains** (no `negate[8]`; unaffected by the retraction) |
| GAP2b | control: same arithmetic shape (range 1..3, `plus[X,7]>=0`), driver a bare-`Int` `∀` instead of a sig cardinality | UNSAT | SAT | — | **SAT** | control fires correctly, isolates the sig domain as the cause (no `negate[8]`; unaffected) |
| GAP2c | control: `some p:P\|#p.f=1 and plus[#p.f,7]=negate[8]` — existential over a sig; both readings agree "exclude" | SAT | UNSAT | UNSAT | **UNSAT** | confirms shared baseline, non-distinguishing; **uses `negate[8]` as a target value (not a domain bound)**, which independently forces exclusion too — the conclusion was already non-distinguishing and is unaffected, but is even more overdetermined than first stated |
| GAP2d (corrected) | nesting variant: `all p:P\|some m:{x:Int\|x∈[1,7]}\|plus[m,7]=p.f`, `fact{all p:P\|p.f∈[−8,−2]}` — **redone properly forced** (`some p:P\|p.f=(0-8)` added as an explicit conjunct so the solver cannot escape via `P` defaulting empty; the original version, with or without `negate[8]`, was vacuous both ways — see the audit below) | SAT | UNSAT (`m` correctly falls back to existential) | UNSAT | **UNSAT (both spellings, once forced)** | **retracted — no anomaly; Defect A alone, correctly falling back, explains it** |

GAP2a/2b are the load-bearing, unaffected findings: **Defect A is confirmed
for sig domains**, and it manifests with a **single, unnested** quantifier
(`GAP2a` has no second quantifier at all in the arithmetic-bearing conjunct)
— so Defect A was never confined to mixed-type doubly-nested quantifiers as
the mission originally scoped it. `all p: SomeSig | <overflow-capable
comparison over p>`, at any nesting depth including zero, silently excludes
instead of rescuing. GAP2d's original claim ("Defect B extends to a
sig-typed enclosing universal") does **not** survive a proper audit: the
original probe never forced `P` to be non-empty, so — exactly like the
`negate[8]`-driven domain-emptiness bug elsewhere — the solver could (and,
it turns out, effectively did) satisfy `all p:P|…` vacuously by leaving `P`
empty, regardless of the fact's own overflow issues. Once forced
non-vacuous (`some p:P|p.f=(0-8)` added), **both** the clean and the
`negate[8]`-spelled fact give forbid UNSAT — i.e. correct behavior, no
anomaly, fully explained by Defect A alone (the inner `m` falls back to
existential, which is correct since `m` genuinely is `∃`).
(`scratchpad/probe/ProbeReaudit3.java`.)

#### The pinned rule, stated operationally for mettle (grounds, never skolemizes; corrected after the round-3 "Defect B" retraction)

Since mettle grounds quantifiers directly (no skolemization step exists to
even ask "at what depth"), and since this round's audit collapsed the
two-defect model down to a **single, uniform, per-variable rule with no
dependence on nesting shape at all**, the operational statement is now much
simpler than the first two passes of this section:

0. **Every quantified variable's own univ/exist classification depends
   *only* on whether ITS OWN quantifier's domain is literally the bare
   `Int`/`seq/Int` builtin** — never on the domain style of any enclosing,
   sibling, or nested quantifier, never on nesting depth (0, 1, 2, or more
   levels), never on nesting type (same-type `∀∀`/`∃∃` or mixed-type
   `∀∃`/`∃∀`), never on the comparison operator, and never on the arithmetic
   operator (`plus` and `mul` both checked). If the variable's own domain is
   the literal `Int`/`seq/Int` builtin, classification is exact (`∀`→univ,
   `∃`→exist). If it is **anything else** — a comprehension
   (`{x:Int|G(x)}`, however simple or complex, however it's guarded), a
   `sig`, or presumably any other non-`Int` type — `DefCond.isUnivQuant`'s
   `isInt()` check fails on that variable's own environment frame, the
   search skips past it, and the classification **defaults to
   existential**, unconditionally.
1. **This default is invisible whenever the variable is genuinely meant to
   classify existential** (bound by `∃`, at positive polarity, in any
   nesting shape) — the fallback coincides with the correct answer, so
   §11.3's rule applies with no deviation. (P1, P3, P5, P11, every bare-`∃`
   control, the `∃∃` same-type cell, GAP2c.)
2. **This default is WRONG whenever the variable is genuinely meant to
   classify universal** (bound by `∀`) **and its own domain isn't literally
   bare `Int`** — the guard should rescue (`∨ of`) but instead excludes
   (`∧ ¬of`), in ANY nesting shape: a lone unnested `∀` (P4, P6,
   `variant-subsetDomain-*`), a `∀` nested inside another `∀` (the same-type
   `∀∀` cell, corrected this round), a `∀` enclosing or enclosed by an `∃`
   (P4, P6), or a `∀` over a `sig` at any depth including zero (GAP2a,
   GAP2d corrected). This is the sole defect (formerly called "Defect A";
   "Defect B" — a supposed second, nesting-position-keyed defect — is
   **retracted**: every one of its decisive probes turned out to depend on
   `negate[8]` as a domain lower bound, and `negate[8]` itself carries a
   permanent overflow flag that silently empties conjunction-shaped domains
   in forbid mode, producing vacuous-truth SAT/UNSAT verdicts that mimicked
   a nesting-position effect. Once re-probed with a clean `(0-8)` bound,
   every "Defect B" cell — P3, the same-type `∀∀` control, the AND/OR
   domain-shape matrix, NP3/NP4, GAP1c, GAP2d — retrodicts as a plain,
   uniform Defect-A case with no separate mechanism needed.)
3. **Single, bare-`Int`-only quantifier of either kind, any polarity** →
   guard behaves exactly per §11.3's ideal statement (P2, P7, P8, P9, P10,
   P12, P14, GAP1a, GAP1b, GAP2b — this is rule 0's "domain is literally
   `Int`" branch restated for the common single-quantifier case).
4. **Comparison sits behind an int-ITE or an `implies` antecedent, and rule
   0/2's precondition (driver's own domain is not bare `Int`) would
   otherwise apply** → **open** (see the Open note above; P9 and P12 show
   the defect NOT firing in this configuration, for reasons not traced to
   source, and this was not re-examined this round); do not guess.
5. **A single comparison whose two operands overflow with different
   classifications** (P13a/b) → **out of scope**, unchanged from §10.7b
   ("ambiguous by hand," ordering question never resolved).

**Conservative typed-defer predicate**, corrected: mettle should implement
rules 0–3 above as bug-compatible verdicts — this is now the entire pinned
rule, verdict-for-verdict, no separate nesting-position case to special-case
— and **typed-defer** (never guess) exactly rule 4's corner: a forbid-mode
overflow-capable comparison reachable only through an int-ITE or an
`implies` antecedent, where the overflow-driving variable's own quantifier
domain is not bare `Int` (comprehension or `sig`). This is **simpler** than
either of the first two passes' predicates: there is one classification
rule (rule 0), applied uniformly regardless of structure, with one open
sub-corner (rule 4). **The practically significant case is unchanged by
this round's retraction**: `all p: SomeSig | <cardinality-overflow
comparison over p>`, at any nesting depth including zero, still silently
excludes instead of rescuing, and mettle must classify a sig-bound (or any
non-`Int`-domain) universally-quantified overflow-driver as existential
unconditionally to stay jar-bug-compatible.

### 10.7d mt-044 round 3: shift semantics pinned, `negate[8]` forbid-confound audit (jar-verified 2026-07-19)

Tech-lead round 3 combined two independent asks: pin the shift operators'
exact mask width and per-op overflow condition (coordinator hand-probes in
`/tmp/.../scratchpad/verify/shifts*.als`, folded in and extended here), and
audit every forbid-mode probe in §10.7b/§10.7c that used `negate[8]` for a
confound the coordinator's own hand-probes had already surfaced. The audit
turned out to invalidate "Defect B" entirely — see §10.7c above, which is
where that correction lives; this section covers the shift semantics and the
audit's mechanics.

Source: `kodkod.engine.bool.TwosComplementInt.shl`/`shr`/`sha` (private `shr`
helper shared by both), read **before** any probe was run, at commit
`794226dd`. Harness: `scratchpad/probe/ProbeShift.java`,
`ProbeDomainAudit.java`, `ProbeReaudit.java`–`ProbeReaudit3.java`
(gitignored), sat4j, symmetry 0, `for 3 but N int`, both `noOverflow`
settings per row.

#### FACT 1 — shift-amount mask width, confirmed from source

`shl` and `shr`/`sha` both compute
`int max = 32 - Integer.numberOfLeadingZeros(width - 1);` where `width =
factory.bitwidth` (the command's `int` scope). This is exactly the
**bit-length of `width-1`**, which is the standard identity for
`⌈log2(width)⌉` at every `width ≥ 1` (no discrepancy at any tested value —
this is a closed-form arithmetic identity, not a coincidence that could
diverge at some untested width). Only the low `max` bits of the shift-amount
operand are ever read (`other.bit(i)` for `i < max` gates every actual
bit-shift step); any higher bit of the amount is **structurally never
consulted for the VALUE computation** — exactly equivalent to masking the
shift amount to its low `⌈log2 w⌉` bits before shifting by the (possibly
still `≥ w`, "everything shifted out") result. Confirmed at bw3/4/5
(coordinator's own probes) and, this round, at **bw6** (untested by the
coordinator, mask should be 3 bits since `⌈log2 6⌉=3`):

| Probe | bw | allow | forbid | Meaning |
|---|---|---|---|---|
| `1<<8=1` | 6 | SAT | UNSAT* | `8 mod 8 = 0` → unshifted, value matches (*forbid diverges — see FACT 2's junk-bit finding, not a mask-formula issue) |
| `1<<8=0` | 6 | UNSAT | UNSAT | value doesn't match either way |
| `1<<6=0` | 6 | SAT | UNSAT | `6` unmasked (within the 3-bit window) shifts `1` fully out of a 6-bit register — genuine overflow, correctly excluded |

Mask formula **confirmed**: `⌈log2 w⌉` bits, exactly as the coordinator's
bw3/4/5 probes indicated, with no discrepancy at bw6.

#### FACT 2 — per-op overflow conditions, exact circuits

**`shl` (own overflow bit):** built as a barrel shifter over the shift
amount's bits from LSB (`i=0`) to MSB (`i=width-1`, note: **not** just up to
the mask width `max` — the outer loop runs the full `width` iterations even
though the VALUE-shifting step is gated `if (i<max)`). At each `i`, if
`other.bit(i)` is set, the circuit ORs in, for every one of the `2^i` bits
about to be (or, for `i≥max`, that *would have been*, had this stage's shift
actually applied) pushed out: **does that bit differ from the bit
immediately adjacent to it, evaluated against the accumulated shifted-so-far
state** (the classic "would restoring the shifted bits change the value"
overflow check, applied incrementally per power-of-two shift stage). For
`i<max` (a real, value-affecting stage) this correctly detects genuine
value-changing overflow — confirmed decisive: `4<<1<0` (bw4, `4<<1=8` wraps
to `-8`) is forbid-**UNSAT** (excluded, correct: `<<` sets overflow when the
shift genuinely wraps).

**Newly-discovered defect: a "junk" (masked-away, `i≥max`) bit of the shift
amount can spuriously set the overflow flag, with ZERO effect on the actual
shifted value.** Because the overflow-check loop runs for every `i` up to
`width`, not just up to `max`, a set bit at position `≥max` still triggers an
`xor(b1,b2)` check against the **already-fully-computed, frozen** masked-shift
state — and if that state happens to have a bit transition at the position
this "should-be-irrelevant" stage inspects, the flag fires anyway. Decisive,
fully deconfounded (no `negate[8]` involved) bw4 matrix, mask=2 bits, junk
bit = bit index 2 (value 4):

| Probe | allow | forbid | Explanation |
|---|---|---|---|
| `5<<0=5` | SAT | SAT | genuinely no shift, no overflow |
| `5<<4=5` | SAT | **UNSAT** | same masked value (`4 mod 4=0`, unshifted) as above, but the junk bit (bit 2 of the amount `4`) is SET, and `5`'s own bit pattern (`0101`) has a transition at the position this junk-bit's check inspects — **spurious overflow** |
| `3<<0=3` | SAT | SAT | control, second shiftee |
| `3<<4=3` | SAT | **UNSAT** | same spurious pattern with a different shiftee — not a fluke |
| `0<<0=0` | SAT | SAT | control |
| `0<<4=0` | SAT | SAT | junk bit set, but shiftee `0`'s uniform bit pattern gives no transition at the inspected position → no spurious trigger, confirming the mechanism is keyed on the *shiftee's* bit pattern at that specific position, not merely "any junk bit set" |
| `1<<4=1` | SAT | **UNSAT** | reproduces with shiftee `1` |
| `1<<8=1` | SAT | **UNSAT** | reproduces at a second junk bit position (bit 3, since literal `8` truncates to bit-pattern `1000`=`-8` at bw4 — see the literal-truncation note below) |

**Rule for `<<`'s overflow flag, exact**: `OR` over **every** bit index `i`
from `0` to `width-1` of the shift-amount operand (not just `0..⌈log2 w⌉-1`)
of: `(that bit is set) AND (the shift-by-`2^i`-stage, applied to the
already-masked-and-shifted intermediate result, would push out a bit
differing from its neighbor)`. mettle must replicate this **exact,
stage-incremental, junk-bit-inclusive** circuit to be bug-compatible — a
"did the true (masked) shifted value change" check alone is **not**
sufficient and will silently disagree with the jar whenever the shift
amount's un-masked high bits happen to be set and the shiftee's own bits
have a transition at the position those junk stages inspect.

**`shr`/`sha` (own overflow bit): always `FALSE`, unconditionally — confirmed
from source** (`shr(Int other, BooleanValue sign)`: `shifted.defCond()
.setOverflows(FALSE, mergeOverflows(other, FALSE))` — the op's own
contribution to both `overflow` and the merge is hardcoded `FALSE`; only
pre-existing overflow already present in either operand propagates through
`mergeOverflows`). `>>` and `>>>` (`sha` and `shr`) **can never self-overflow
on clean operands**, confirmed with several probes free of `negate[8]`:

| Probe | allow | forbid |
|---|---|---|
| `1 >>> 1 = 0` | SAT | SAT |
| `1 >> 1 = 0` | SAT | SAT |
| `(0-1) >> 1 = (0-1)` | SAT | SAT (sign-fill keeps `-1`, no overflow) |
| `3 >>> 3 = 0` | SAT | SAT |

A masked-to-large (`≥w`) shift amount does **not** change this — `>>`/`>>>`
still never self-overflow regardless of amount magnitude, since their own
overflow bit is unconditionally `FALSE` independent of the amount's bits at
all (unlike `shl`'s junk-bit defect, which is specific to `shl`'s own
value-change-detection circuit).

**Confound found and corrected mid-round**: two of the coordinator's own
hand-probes (`negate[8]>>1=negate[4]`, `negate[8]>>5=negate[4]`) showed
forbid-**UNSAT**, which — taken at face value — would have suggested `>>`
*can* self-overflow. Both are confounded by `negate[8]`'s own permanent
poison (FACT 3 below): re-run with the clean `(0-8)` spelling, **both flip
to forbid-SAT** — `>>` never overflows here; the UNSAT was entirely
`negate[8]`'s own flag, unrelated to the shift. This is a direct instance of
exactly the audit risk the coordinator flagged, caught and corrected within
this same round.

#### FACT 3 — `negate[8]` carries a permanent forbid-mode overflow flag; audit of every prior use

`negate[8]` desugars to `minus[0,8]` (`Int.negate()` = `zero.minus(this)`),
and representing the literal `8` itself already requires wraparound at bw4
(max positive representable is 7) — so the subtraction that produces `-8`
genuinely overflows internally, and `negate[8]`'s own `DefCond.accumOverflow`
is `TRUE` **everywhere it appears**, permanently, regardless of context.
Decisive:

| Probe | allow | forbid |
|---|---|---|
| `negate[8] = negate[8]` | SAT | **UNSAT** (self-equality fails — the term is intrinsically poisoned) |
| `negate[7] = negate[7]` | SAT | SAT (clean control) |
| `(0-8) = (0-8)` | SAT | **SAT** (the peephole-folded MIN literal is a clean `IntConstant`, no arithmetic, no overflow flag) |
| `(0-7) = (0-7)` | SAT | SAT (ordinary relational set-difference, unrelated mechanism, always clean) |

**`(0-8)` is confirmed as the clean, overflow-free spelling of MIN for every
future forbid-mode probe.** `negate[8]`, as a bare constant, has empty
`vars()` (no bound variable), so it always classifies existential (per
§11.3's own text: constants are existential) and its `TRUE` overflow forces
`AND ¬of` unconditionally at positive polarity — meaning **any comparison
containing `negate[8]` is forced false**, and — far more perniciously — a
domain comprehension guard containing `negate[8]` (`x>=negate[8]`) is
**forced false for every candidate `x`, emptying the domain entirely**,
independent of `x`. Confirmed directly:

| Probe | allow | forbid |
|---|---|---|
| `#{x:Int\|x>=negate[8] and x<=negate[2]} = 7` | SAT | **UNSAT** (does NOT have 7 members) |
| `#{x:Int\|x>=negate[8] and x<=negate[2]} = 0` | UNSAT | **SAT** (the domain IS empty) |
| `#{x:Int\|x>=(0-8) and x<=negate[2]} = 7` | SAT | **SAT** (clean bound: genuinely 7 members) |
| `#{x:Int\|x>=(0-8) and x<=negate[2]} = 0` | UNSAT | **UNSAT** (clean bound: genuinely non-empty) |

**Audit outcome — every forbid-mode probe in §10.7b/§10.7c that used
`negate[8]`, and whether its conclusion survives:**

| Probe / location | Used `negate[8]` as | Conclusion survives? |
|---|---|---|
| §10.7b "negate[k] works uniformly for every k in 1..8" | allow-mode value check only | **survives** — that claim was explicitly about allow-mode *values*, never forbid-mode overflow behavior |
| §10.7b `div[MIN,-1]` probes (`div[negate[8],negate[1]]`) | allow-mode value check only | **survives** — allow mode, no overflow guard consulted |
| §10.7b/§10.7c bare-∃ control (`some m:{1..7}\|plus[m,7]=negate[8]`) | target value (not a domain bound) | **survives, but was overdetermined** — the reported UNSAT is forced by *both* the (correct) exist-classified exclusion of the overflowing `m` *and* `negate[8]`'s own independent poison; re-run with clean `(0-8)` target gives the same UNSAT, confirming the qualitative conclusion but showing the original evidence conflated two mechanisms |
| GAP2c (`plus[#p.f,7]=negate[8]`) | target value (not a domain bound) | **survives, already flagged non-distinguishing** — both readings agreed "exclude" before this audit; now doubly overdetermined, still non-distinguishing, no change to any rule |
| **P3 and every domain spelled `{x:Int\|x>=negate[8] and x<=negate[2]}`** (P3 itself, the same-type `∀∀` control, the AND/OR domain-shape matrix, NP3, NP4, GAP1c, GAP2d) | **domain lower bound** | **does NOT survive** — every one of these flips from an apparent anomaly (or, for the `∀∀` control, an apparent "correct rescue") to a clean Defect-A-only retrodiction once re-probed with `(0-8)`; full correction in §10.7c above |

**Rule-0/GAP2's core sig-domain finding (GAP2a/GAP2b) used no `negate[8]`
anywhere and is unaffected** — it stands exactly as reported: a
genuinely-universal sig-bound variable is misclassified as existential,
unconditionally, at any nesting depth including zero.

### 10.9 mt-043 String probes (jar-verified 2026-07-18)

Harness dumps `A4Solution.toString()` (universe + `String` relation).

| # | Case | Observation |
|---|---|---|
| S1 | `run { some s } for 3 but 3 String` (non-exact) | **ERROR** `Sig "String" must have an exact scope.` — a non-exact `String` scope is rejected pre-solve |
| S2 | `... exactly 3 String`, one field `s: String`, no literals | universe tail `…, 7, "String1", "String0", "String2"`; `String={"String1","String0","String2"}` — **padding atoms are the strings `"String0"`, `"String1"`, `"String2"` (with their quote characters), NOT `unused%d`**; appended **after** ints; **HashSet order** (note `"String1"` precedes `"String0"` — nondeterministic in the jar) |
| S3 | `exactly 3 String` + fact `p.s = "hello"` | `String={"String1","String0","hello"}` — one referenced literal + two padding atoms fill the scope |
| S4 | 3 referenced literals `"x"/"y"/"z"`, `exactly 1 String` | `String={"z","y","x"}` — **an `exactly N String` scope is NOT truly exact: it expands to `max(N, #referenced-literals)`** (reporter: "Sig String expanded to contain all 3 String constant(s)"); no padding added since 3 ≥ 1 |
| S5 | one literal `"only"`, **no** `String` scope | `String={"only"}` — `maxstring = −1` default: exactly the referenced literals, no padding |
| S6 | literal only in a **top-level** fact `fact { Q.s = "topfact" }` | `String={"topfact"}` — top-level (module) facts **are** scanned for literals |
| S7 | literal only in an **uncalled** pred body | `String={}` — literals in unreferenced pred/fun bodies are **not** collected (the walk is over the command formula + all facts + field decls, recursing only into *called* funcs) |

### 10.10 mt-043 seq probes (jar-verified 2026-07-18)

| # | Case | Observation |
|---|---|---|
| Q1 | `sig P { f: seq Int }` for `2 but 3 seq, 4 int` | `seq/Int={0,1,2}` (maxseq 3); `P<:f` tuples are arity 3 `P$0->0->-8`, `P$0->1->7` — a `seq X` field is `seq/Int -> lone X` |
| Q2 | index 1 used, index 0 unused (`(1->E) in R.f and no ((0->E)&R.f)`) | **UNSAT** — the **contiguity fact** `dom(f) − dom(f).(Int/next) ⊆ Int/zero` forces the used indices to be a prefix from 0 |
| Q3 | indices 0 and 1 both used | **SAT** control |
| Q4 | `seq/Int` at `for 2`, `for 2 but 5 seq`, `for 6` | maxseq **2**, **5**, **6**; `seq/Int={0..maxseq−1}` — bare maxseq = `min(overall, max(bw))`; `for N seq` overrides it, **independent of overall** |

#### 10.10a mt-046 seq implementation probes (jar-verified 2026-07-19)

Follow-up probes taken while implementing mt-046 (`OracleShim`, sat4j, sym 0,
noOverflow true), closing the §14 per-owner-vs-global ambiguity and
differentially verifying the clean-room `util/sequniv`/`seqrel`/`sequence`
bodies. All jar-pinned; the mismatches were mettle clean-room bugs, fixed
black-box.

| # | Case | Observation |
|---|---|---|
| mt046-contig | two owners: `p1.f` uses indices {0,1}, `p2.f` uses {1} without {0} | **UNSAT** → the contiguity fact is **PER-OWNER**, not global (a global projection over the union {0,1} would be SAT). Control (`p2.f` uses {0} only) → SAT. So contiguity is emitted inside `all this: owner |`, over `this.f`'s index column. |
| mt046-maxseq-clamp | `for 6 but 3 int` | maxseq **3** (clamped to `max(bw 3)=2^2−1=3`); `for 6 but 4 int` → 6 (no clamp). |
| mt046-idxOf | `e` at indices {0,2}: `idxOf`/`lastIdxOf` | jar `idxOf = 0` (first/min), `lastIdxOf = 2` (last/max). mettle's clean-room `util/sequniv`/`seqrel`/`sequence` had the two closures **swapped** (`idxOf` used `^prev`→max, `lastIdxOf` used `^next`→min) — **fixed**: `idxOf = indsOf − indsOf.^next`, `lastIdxOf = indsOf − indsOf.^prev`. |
| mt046-afterLast | `afterLastIdx[empty]`, `add[empty, e]` | jar `afterLastIdx[empty] = 0` (seq/Int) / `ord/first` (ordered SeqIdx), so `add[empty, e] = {0 -> e}` (length 1). mettle's `afterLastIdx = lastIdx.next` gave `none` for empty (`none.next`), leaving `add`/`append` a no-op — **fixed** (see mt046-noncontig for the final body). |
| mt046-noncontig | `sequniv/afterLastIdx[{1->e}]` (gapped, non-contiguous) | jar `= 0` (SAT), `= 2` UNSAT; `add[{1->e}, e] = {1->e}+{0->e}` SAT, `…+{2->e}` UNSAT — **`afterLastIdx` is the smallest UNUSED index, NOT `lastIdx.next`** (they differ off the contiguous-prefix domain, reachable because sequniv funs accept arbitrary `Int->univ`). Tech-lead review probe; the first fix (`lastIdx.next + empty-case`) was wrong here. Final body: `(seq/Int − inds[s]) − (seq/Int − inds[s]).^next` (min of the unused set), all three modules. |
| mt046-full | `sequniv/afterLastIdx[{0,1,2}->e]` (every `seq/Int` index used, maxseq 3) | jar `no afterLastIdx[s]` SAT, `= 3` UNSAT — full sequence has **no** after-index (min of an empty unused set), confirming the min-unused reading over `lastIdx.next` (which would give 3). |
| mt046-seqrel-gap | `seqrel/afterLastIdx[{mid->e}]`, exactly 3 `SeqIdx` | jar `= firstIdx` SAT, `= finalIdx` UNSAT — same min-unused semantics in the ordered bare-relation module (`(SeqIdx − inds) − (SeqIdx − inds).^(ord/next)`). `util/sequence` is domain-constrained contiguous by its `Seq` sig fact, so both forms agree there; min-unused adopted uniformly. |
| mt046-natural | `natural/add`/`sub`/`lt` on small ranks | jar and mettle agree (1+1=2, 2−1=1, 0<1) — the `util/natural` rank arithmetic body is correct as-is (no fix). |

### 10.11 mt-043 first-order skolemization probes (jar-verified 2026-07-18)

| # | Case | Observation |
|---|---|---|
| K1 | `run foo { some x: A | x=x } for 3` | instance carries skolem `$foo_x = {A$0}` — a top-level `∃` skolemizes to `$<cmdLabel>_<var>` |
| K2 | anonymous `run { some x: A | … }` (label `run$1`) | skolem `$x` — a label containing `$` drops the prefix (source `skolem()`); read-back adds one `$` and uniquifies (`un.make("$"+n)`) |
| K3 | `run bar { all y: A | some x: A | x!=y }` | **no** `$` skolem in the instance — an `∃` nested under an `∀` is **not** skolemized at depth 0 |
| K4 | SB-0 count of `run { some x: A | x=x } for 3` | jar **12** vs a no-FO-skolem count **7**: `12 = Σ over non-empty subsets |subset|` (the jar enumerates each skolem-constant witness); this is the `skip_fo_skolem` divergence mt-047 closes |

### 10.12 mt-043 symmetry-breaking probes (jar-verified 2026-07-18)

| # | Case | Observation |
|---|---|---|
| Y1 | `run { some A } for 3`, SB=20 vs SB=0 | count **3** vs **7**, verdict **SAT** both — SB changes the enumerated count, never the verdict; SB=0 is the raw count (matches probe T3) |

---

## Rung-4 semantics extensions (mt-043)

> **Sections §11–§16 were added by mt-043 for Rung 4.** They pin the behavior the
> Rung-4 implementation beads (mt-044 integers, mt-045 String, mt-046 seq, mt-047
> FO skolemization, mt-048 symmetry) are written from, plus the posture inputs to
> [ADR-0012](../adr/0012-rung4-integers-strings-counting.md). Provenance is the
> same as the rest of this doc: Java read at commit `794226dd`, every rule carried
> by a source citation **and** a decisive jar probe (§10.7–§10.12), the jar
> winning any tie. Facts pinned here promote the SEMANTICS_LEDGER corners
> (integer wraparound & bitwidth, cardinality `#`, `seq`, String).

## 11. Integer arithmetic at bitwidth (Rung 4, mt-043)

### 11.1 The op mapping (surface → Kodkod `IntExpression`)

`+` and `-` on relations are **relational** union/difference (`ExprBinary` cases
`PLUS`/`MINUS`); there is **no `int`↔`Int` coercion** in 6.2.0 (resolution §4.5),
so integer arithmetic is reached **only** through the `fun/…` operator forms that
`util/integer`'s functions expand to. The mapping (`TranslateAlloyToKodkod.
visit(ExprBinary)`, jar-probed §10.7):

| Surface (`util/integer` fun / operator) | `ExprBinary.Op` | Kodkod `IntExpression` |
|---|---|---|
| `plus`/`add` / `fun/add` | `IPLUS` | `a.plus(b)` |
| `minus`/`sub` / `fun/sub` | `IMINUS` | `a.minus(b)` |
| `mul` / `fun/mul` | `MUL` | `a.multiply(b)` |
| `div` / `fun/div` | `DIV` | `a.divide(b)` |
| `rem` / `fun/rem` | `REM` | `a.modulo(b)` |
| `<<` | `SHL` | `a.shl(b)` — logical left |
| `>>` | `SHA` | `a.sha(b)` — **arithmetic** (sign-extending) right |
| `>>>` | `SHR` | `a.shr(b)` — **logical** (zero-fill) right |
| unary `- e` (int negation) | `IMINUS` of `0,e` | via `0.minus(e)` (`util/integer/negate`) |
| `#e` | — (`ExprUnary CARDINALITY`) | `cset(e).count()` |
| `int[e]` / `sum e` (`CAST2INT`) | — | `sum(cset(e))`, with the `int[Int[x]]≡x` peephole |
| `Int[ie]` (`CAST2SIGINT`) | — | `cint(ie).toExpression()` |
| `sum x: S | ie` | `ExprQt.SUM` | `cint(ie).sum(decls)` |
| integer `c => ie1 else ie2` | `ExprITE` | `cond.thenElse(ie1, ie2)` (a **formula** condition; relational/int branches use Kodkod `thenElse`, a formula-valued ITE desugars to `(c⟹l) ∧ (¬c⟹r)`) |

The one peephole is on **`MINUS`** (not `IPLUS`, correcting §2.4's earlier note):
`0 - (max+1)` folds to the constant `min`, letting the most-negative literal be
written (`TranslateAlloyToKodkod`, `ExprBinary` `MINUS` case).

**mettle:** these become `als_core::ir::IntExprKind::{Plus,Minus,Mul,Div,Rem,Shl,
Shr,Sha,Sum,Card,…}` over the two's-complement encode layer mt-033 already built
for `Const`/`Card`/`AtomToInt`; the **evaluator matched-pair rule (mt-034)
extends over every new op** so the encoder↔evaluator differential keeps its teeth
(ADR-0012).

### 11.2 Two's-complement wraparound (allow mode) — exact per-op semantics

`IntEncoding.TWOSCOMPLEMENT` at the command bitwidth `w` (default 4, range
`−2^{w-1} .. 2^{w-1}−1` = −8..7). With `noOverflow=false` every op is pure
`w`-bit two's-complement, **wrapping** (`Options.setNoOverflow(false)`;
`TwosComplementInt`, jar-probed):

- **`plus`/`minus`/`mul`** wrap (`plus[7,7]=−2`, `mul[3,3]=−7`; I5).
- **`div` (`divide`) truncates toward zero** (Java `/`): `div[-5,2]=−2`,
  `div[5,-2]=−2`, `div[-5,-2]=2` (I1/I2). It is a non-restoring signed division
  (`nonRestoringDivision`, Parhami).
- **`rem` (`modulo`) takes the sign of the dividend** (Java `%`): `rem[-5,2]=−1`,
  `rem[5,-2]=1` (I3).
- **Shifts:** `<<` logical-left, `>>` **arithmetic** (sign-extending) right, `>>>`
  **logical** (zero-fill) right — `4<<1=8`, `(−8)>>1=−4`, `(−8)>>>1=4` (I4).
  (Note the Kodkod method names `shr`/`sha` are the *opposite* convention to the
  surface `>>`/`>>>`: surface `>>` → `sha`, surface `>>>` → `shr`.) **The shift
  AMOUNT is masked** (mt-044 round 3, §10.7d, jar-verified at bw3/4/5/6, source
  `TwosComplementInt.shl`/`shr`): only the low `⌈log2 w⌉` bits of the amount
  operand are ever consulted (`32 - Integer.numberOfLeadingZeros(w-1)` in the
  source, the standard bit-length identity, no discrepancy at any width) —
  equivalent to masking the amount to `amount mod 2^⌈log2 w⌉` before shifting
  by the (possibly still `≥ w`, i.e. "everything shifted out") result. At bw4
  (mask 2 bits): `1<<4=1` (`4 mod 4=0`, unchanged), `1<<5=2` (`5 mod 4=1`). At
  bw5 (mask 3 bits): `1<<8=1` (`8 mod 8=0`), `1<<5=0` (`5<8` unmasked, shifts
  fully out of a 5-bit register). Forbid-mode overflow for shifts is pinned in
  full, per op, in §10.7d — in short: `<<` sets a genuine overflow flag when
  the shift truly changes the represented value (confirmed: `4<<1<0` is
  forbid-UNSAT, `4<<1=8` wraps), but also has a **jar-specific defect**: a
  masked-away ("junk") high bit of the shift amount can spuriously set the
  overflow flag with zero effect on the actual shifted value, depending on the
  shiftee's own bit pattern — mettle must replicate the jar's exact
  stage-incremental circuit (§10.7d FACT 2), not just "did the masked value
  change." `>>`/`>>>` **never self-overflow** on any operand (own overflow bit
  is unconditionally `FALSE` in the source; only pre-existing overflow already
  present in either operand propagates through).
- **Division/remainder by zero (allow mode) produce jar-specific values, not a
  trap:** `rem[x,0]` uniformly yields **x** (the dividend — `rem[3,0]=3`,
  `rem[-5,0]=-5`, `rem[0,0]=0`, `rem[-8,0]=-8`, I7). **`div[x,0]` is now fully
  characterized (mt-044, §10.7b — a jar-verified closed form, no longer a
  residual): `div[x,0] = -sign(x)`** — uniformly **1** for **every** negative
  dividend including MIN (`div[-8,0]=1`, same rule as `div[-1,0]=1`, no special
  case at MIN), **0** at `x=0`, and **−1** for every positive dividend
  (`div[3,0]`, `div[5,0]`, `div[7,0] = −1`, already pinned pre-mt-044). The full
  16×16 sweep (§10.7b) also confirms `div`/`rem` match Java `/` (truncating) and
  `%` (sign-of-dividend) exactly for **every** `(a,b)` with `b≠0` except one:
  **`div(MIN,−1) = -8`** (not the previously-stated `1` — that "1" was an
  artifact of a probe-spelling bug, `(0-1)` silently meaning `div[MIN,0]` rather
  than `div[MIN,-1]`; see §10.7b for the full correction and decisive
  re-verification). `-8` is the ordinary two's-complement division-overflow
  wraparound (`wrap(-MIN)=wrap(8)=-8`, the same INT_MIN/−1 behavior as Java/C/x86
  `IDIV`), not an exotic algorithm artifact. All of these matter **only** in
  allow mode; in forbid mode they are overflow (§11.3) and their instances are
  excluded, so mettle need only reproduce them for `--allow-overflow` fidelity.

`#e` cardinality is itself a two's-complement `IntExpression` (`count()`), so a
count exceeding `2^{w-1}−1` **wraps** in allow mode (`#A=8` at bw 4 reads as −8,
I12) and is an **overflow** in forbid mode (I12/I13) — the "cardinality overflow
interplay" corner.

### 11.3 Forbid mode — the Milicevic/Jackson polarity rule

**This section states the *ideal* Milicevic/Jackson rule as background — it is
the rule the jar's authors intended and the rule that holds for every
single-quantifier formula and every same-type nested quantifier (`∀∀`, `∃∃`).
It is subordinate to the ACTUAL jar rule, which additionally has two
jar-specific defects for mixed-type doubly-nested quantifiers (`∀∃`/`∃∀`),
pinned in full — trigger conditions, retrodiction table, ≥6 new decisive
probes, and the conservative typed-defer boundary — in
[§10.7c](#107c-mt-044-mixed-nesting-forbid-mode-trigger-pinned-jar-verified-2026-07-19).
Read this section for the mental model, then §10.7c for what mettle must
actually implement to be bug-compatible.**

**This is the subtle corner. Forbid mode is NOT a flat `goal ∧ ¬overflow`.** Each
`Int` carries an accumulated-overflow circuit; when an `Int` becomes a `Formula`
(at a comparison `eq`/`lt`/`lte`/`gt` or an int `=`), Kodkod inserts an
overflow-guard whose **direction depends on the formula's polarity and on whether
the overflowing operand depends on a universally- or existentially-quantified
variable**. Source: `DefCond.ensureDef` (`kodkod.engine.bool`) — pinned verbatim
in behavior:

```
if (!noOverflow) return value;                       // allow mode: raw wrap
for each int operand with accumulated overflow of:
  classify it as "universally-quantified" (depends on a var bound by an
  enclosing ∀ at the current polarity) or "existentially-quantified" (all else,
  incl. constants and free vars).
if NOT negated (positive polarity):
  univ operands:  value := value  OR  of      // overflow makes the atom TRUE
  exist operands: value := value AND ¬of       // overflow makes the atom FALSE
else (negative polarity): the two are swapped.
```

**Behavioral reading (the rule to implement):** in forbid mode an overflowing
arithmetic subterm forces its enclosing atomic formula to the truth value that
**removes the overflowing instance from the answer set** — a witness that only
satisfies a `run`/positive existential *by overflowing* is rejected (`AND ¬of`),
while a `∀` is **not** falsified by an overflowing binding (`OR of`, the body
holds vacuously there). Negative polarity (a `check`'s negated body, an `implies`
antecedent, `not`) swaps the two. Decisive probes:

- **Positive existential** (`plus[7,7] < 0`, I9): allow **SAT** (−2<0), forbid
  **UNSAT** — the overflowing witness is excluded (`AND ¬of`).
- **Universal position** (`all n: Int | plus[n,7] >= n`, I11): allow **UNSAT**
  (fails at n=7, 7+7 wraps), forbid **SAT** — the overflowing binding is forced
  true (`OR of`), so the ∀ holds. This is the case a naive `∧ ¬overflow` gets
  wrong.
- **Div-by-zero / MIN÷−1 / rem-by-zero** set the overflow circuit (`divide`:
  `divByZero ∨ (this=MIN ∧ other=−1)`; `modulo`: accumulates `divByZero`), so
  each is excluded in forbid mode at positive polarity (I10) — even the reflexive
  `div[5,0]=div[5,0]`.
- **Cardinality** `#e` feeds the same machinery (I12/I13).

mettle already mirrors this in the mt-034 evaluator's overflow tracking and the
mt-033 encoder for the Rung-3 slice (`Const`/`Card`/`AtomToInt`); mt-044 extends
the **same** polarity-threaded guard over arithmetic/`sum`/int-ITE so encoder and
evaluator stay the matched pair. The polarity `Pol` thread from mt-038's HO
skolemization (§10.6) is the existing seam for "current polarity"; the
univ-vs-exist classification keys on whether an overflowing operand's free
variables include a variable bound by an enclosing `∀` at that polarity.

**The actual jar rule (corrected, round 3, 2026-07-19 — a "second defect" was
reported and then retracted; see below):** the ideal statement above is
exactly what the jar does *except* for **one** defect, not two, rooted in a
single mechanism: `DefCond.isUnivQuant`'s `isInt()` check recognizes only the
literal bare `Int`/`seq/Int` builtin as "an Int domain," full stop. Any
quantified variable whose **own** domain is anything else — a comprehension
(`{x:Int|G(x)}`, however it's guarded), or a `sig` — silently has its
classification default to **existential**, unconditionally, at **any**
nesting depth (0, 1, 2, or more) and **any** nesting shape (a lone `∀`, a
same-type `∀∀`/`∃∃` nesting, or a mixed-type `∀∃`/`∃∀` nesting) — the
defect is a **per-variable** rule with no dependence on surrounding
structure at all. This is invisible whenever the affected variable is
genuinely meant to classify existential (the fallback already matches) and
**wrongly excludes instead of rescuing** whenever it is genuinely meant to
classify universal. `skolemDepth` was swept 0 through 4 and off and is
conclusively **not** the trigger of anything here (refutes the tech lead's
original hypothesis). A first pass of this investigation additionally
reported a second, independent "nesting-position" defect (existential nested
inside a range-guarded universal disables the guard, fixed by rephrasing the
guard as a disjunction) — **this is retracted**: every one of its decisive
probes turned out to use `negate[8]` (`=minus[0,8]`, itself an overflowing
computation) as a domain lower bound, and `negate[8]` carries a permanent
forbid-mode overflow flag that silently empties conjunction-shaped domains,
producing vacuous-truth verdicts that mimicked a nesting-position effect;
re-probed with the clean `(0-8)` MIN spelling, every one of those cells
retrodicts as a plain instance of the single defect above, with no separate
mechanism needed (full audit: §10.7d). **The practically significant case is
unaffected by the retraction**: `all p: SomeSig | <cardinality-overflow
comparison over p>` — the most common corpus shape this rule touches —
silently gets the wrong verdict (excludes rather than rescues), at any
nesting depth including zero. Full mechanism, source citations, the
skolemDepth matrix, a 100% retrodiction over the P1–P14 probe set, ≥6 new
decisive probes, and the round-3 retraction/audit are in
[§10.7c](#107c-mt-044-mixed-nesting-forbid-mode-trigger-pinned-jar-verified-2026-07-19)
and [§10.7d](#107d-mt-044-round-3-shift-semantics-pinned-negate8-forbid-confound-audit-jar-verified-2026-07-19).
Shift-specific overflow semantics (mask width, per-op overflow conditions,
including a jar-specific "junk shift-amount bit spuriously flags overflow"
defect in `<<`) are pinned in §10.7d and summarized in §11.2's shift bullet.

### 11.4 LEDGER note

This section is the evidence for **LEDGER-005 (integer wraparound & bitwidth)**
and **LEDGER-006 (cardinality `#`)** below. The LEDGER-001 overflow *switch* is
unchanged (canonical default = forbid); §11.3 pins what "forbid" *means* per op
and polarity, which LEDGER-001 deferred to "the Rung-3 integer work".

## 12. Integer builtin relations `Int/min|max|next|zero` (Rung 4, mt-043)

The `A4Solution` constructor (jar source, verified) builds four constant relations
over the integer atoms, **always** when the model uses integers (bitwidth ≥ 1 —
and `shouldUseInts` is hard-coded `true` in `ScopeComputer`, so bitwidth defaults
to 4 and these are effectively always allocated). At bitwidth `w`, `min = −2^{w-1}`,
`max = 2^{w-1}−1`:

| Relation | Arity | Exact bound (`boundExactly`) | at bw 4 |
|---|---|---|---|
| `Int/min` | 1 | `{ min }` | `{−8}` |
| `Int/max` | 1 | `{ max }` | `{7}` |
| `Int/zero` | 1 | `{ 0 }` | `{0}` |
| `Int/next` | 2 | `{ i → i+1 : min ≤ i < max }` | `{−8→−7, …, 6→7}` |
| `seq/Int` | 1 | `{ 0 … maxseq−1 }` | (see §14) |
| `String` | 1 | the string atoms (§13) | — |

All are `boundExactly` **constants** (no free tuples), so they are symmetry-inert.
They are allocated in the bounds builder, not the lowerer.

**How `util/integer` maps onto them (jar-probed, §10.8) — a simplifying surprise:**

- `fun/min` / `fun/max` (and thus `util/integer`'s `min`/`max` no-arg funcs)
  translate to the **integer constants** `IntConstant.constant(min/max)`, **not**
  the `Int/min`/`Int/max` relations (`TranslateAlloyToKodkod.visit(ExprConstant)`
  cases `MIN`/`MAX`). So the `Int/min`/`Int/max` relations, though bounded, are
  effectively unreferenced by translation.
- `fun/next` translates to the `Int/next` **relation** (`visit(ExprConstant)` case
  `NEXT` → `KK_NEXT`); `util/integer`'s `next` = `Int/next`, `prev` = `~(Int/next)`,
  `nexts`/`prevs` = `^next`/`^prev`. `7.next` and `(−8).prev` are empty (chain
  endpoints, I15).
- `Int/zero` is referenced only by the seq contiguity fact (§14) and
  `util/integer/pos`/`neg`-style comparisons (via the constant 0).
- `int2elem`/`elem2int` (mapping a rank to/from a `util/ordering`-style element)
  are ordinary library funcs over `^(~next)` — no builtin needed.

**mettle:** allocate `Int/next` and `Int/zero` in the bounds builder (needed by
`next`/`prev`/`nexts`/`prevs` and by seq); `min`/`max` may lower as int constants
(matching the jar) rather than as relation joins. This is what unlocks the 39
`lower:lowering` "integer-ordering builtin" defers (mt-044): they are commands
using `util/integer`'s `next`/`prev`/`min`/`max`/`nexts`/`prevs` and the
arithmetic funcs, all of which reduce to §11's ops plus `Int/next`.

This section is the evidence for the `util/ordering`-adjacent integer half of
**LEDGER-005**; it replaces the §1.4′ B18 stub's forward reference.

## 13. String semantics (Rung 4, mt-043)

**String atoms are minted in scope/universe computation** (`ScopeComputer.compute`
→ `A4Solution` ctor), never in the bounds builder or lowerer. The exact rule
(jar source + probes §10.9):

1. **Referenced-literal collection.** `Command.getAllStringConstants(sigs)` walks,
   collecting every `ExprConstant.STRING`: the command's formula **and every
   parent command's formula**, plus **every reachable sig's appended facts and
   field-declaration expressions**, recursing into the bodies of **called**
   funcs/preds (`ExprCall` visits `fun.getBody()`). Top-level module facts **are**
   included (S6); a literal reachable only through an **uncalled** pred is **not**
   (S7). The result is a `HashSet<String>` — its iteration order is
   **nondeterministic in the jar** (S2 shows `"String1"` before `"String0"`); the
   atom strings **include their surrounding quote characters** (the atom for the
   literal `"hi"` is the 4-char string `"hi"`).
2. **The `maxstring` scope.** Default `−1` ("unspecified" — collect referenced
   literals only, no padding, S5). A `String` scope is set **only** by a `for …
   but N String` clause, which **must be exact** — a non-exact `String` scope is a
   pre-solve **error** (`Sig "String" must have an exact scope.`, S1); it may not
   be set twice.
3. **Padding fill.** After collection, while `set.size() < maxstring`, add
   synthetic atoms named **`"String0"`, `"String1"`, `"String2"`, …** (the strings
   `"String" + i`, quote characters included) — **NOT `unused%d`** (S2; see the
   discrepancy note below). Padding stops at `maxstring`.
4. **Expansion (an `exactly N String` scope is not truly exact).** If the number
   of *referenced* literals exceeds `maxstring`, the scope is **expanded** to fit
   all of them (reporter: "Sig String expanded to contain all N String
   constant(s)") — the effective String population is **`max(N, #referenced)`**
   (S4). No padding is added in that case.
5. **Universe placement & bounds.** The string atoms are appended **last** in the
   universe (after sig atoms and after the ascending int atoms — §1.3), and the
   `String` relation is `boundExactly` to exactly them. Each literal also gets its
   own private singleton relation (`s2k` map) so `= "lit"` resolves.

There is **no richer String algebra in 6.2.0** — only equality/inequality/set
membership over these atoms (confirmed: string atoms are ordinary uninterpreted
atoms; `#`, `in`, `=`, `!=` are the operations, exactly as for any unary sig).

> **⚠ Discrepancy flagged (mt-043).** LIMITATIONS.md, docs/STATE.md and the mt-043
> bead brief describe the padding atoms as `unused%d`. That is **wrong for the
> pinned jar** — the source mints `"String" + i` (`ScopeComputer.compute`, S2).
> The `unused%d` naming is a **different** mechanism: at **instance read-back**,
> `A4Solution.rename` labels any *universe atom no sig claims* as `"unused" +
> unused` for display (`A4Solution.java`, the loop before skolem read-back). The
> two were conflated. mettle must mint `"String" + i` padding (deterministically
> ordered — the jar's HashSet order is not reproducible and need not be, since
> string atoms are symmetric so verdict/SB-0-count are unaffected by their order).
> The existing translation-ref §1.3 already correctly said `"String0"…`; only the
> downstream docs drifted. This resolves the `scope` defer family (mt-045,
> `fm2cfs.als`).

This section is the evidence for **LEDGER-007 (String)** below.

## 14. `seq` semantics (Rung 4, mt-043)

**`seq/Int` bound.** The `seq/Int` builtin unary relation is `boundExactly` to the
first `maxseq` non-negative integer atoms `{0 … maxseq−1}` (already exact in
mettle, mt-030). `maxseq` (jar `ScopeComputer`): unspecified ⇒ `overall` if the
command gave an overall scope, else `4`, then **clamped to `max(bw)` = `2^{w-1}−1`**
(=7 at bw 4); a `for N seq` clause sets it directly to `N`, **independent of the
overall scope** (Q4). Setting the bitwidth resets `maxseq` to 0, so the seq clause
/ default is applied after.

**`seq X` field desugar.** A field `f: seq X` desugars to **`f: seq/Int -> lone X`**
— the stored relation is `owner -> Int_index -> X`, with a `lone` on the value
column (Kodkod op `ISSEQ_ARROW_LONE`); the index column's upper bound is `seq/Int`
(so at most `maxseq` entries) (Q1).

**The contiguity fact (where sequence-ness is enforced).** Alongside the
`lone`-value arrow constraint, `TranslateAlloyToKodkod` (the `ISSEQ_ARROW_LONE`
branch) synthesizes exactly one extra fact per seq field: projecting the field to
its index column `dom`,

```
dom(f) − dom(f).(Int/next)  ⊆  Int/zero
```

i.e. the only used index without a used predecessor is `0` ⇒ the used indices form
a **contiguous prefix from 0**. A seq that uses index 1 without index 0 is
therefore **UNSAT** (Q2); a proper prefix is SAT (Q3). This is the *only* implicit
fact `seq` introduces (besides the `lone` value multiplicity); it is generated at
**lowering** (field-fact assembly, §2.5), using the `Int/next` and `Int/zero`
builtin relations from §12.

**`util/sequniv` / `util/seqrel`.** These are ordinary library modules over the
`seq/Int` index domain; their functions (`isSeq`, `elems`, `inds`, `lastIdx`,
`add`, `setAt`, `subseq`, …) lower as normal funcs — the only builtin-special
pieces are `seq/Int` (bound above) and the contiguity fact. The clean-room
stdlib's `natural`/`sequence`/`seqrel` rank-arithmetic bodies (the mt-015 judgment
calls) are verified differentially when mt-046 exercises them (the "clean-room
stdlib body semantics" Ledger corner — not re-pinned here; verify at
implementation).

This section is the evidence for **LEDGER-008 (`seq`)** below.

## 15. First-order skolemization (Rung 4, mt-043)

ADR-0011 deliberately deferred FO skolemization; §2.3 pinned it structurally.
This section pins it precisely enough that mt-047 can make the `skip_fo_skolem`
counting family exact, and instances *show* skolem witnesses (drop-in display).

**When it fires (depth-0 rule).** `A4Options.skolemDepth = 0` (default; Kodkod
`Options.skolemDepth` also 0). Kodkod's `Skolemizer` NNF-threads a `negated`
polarity and skolemizes a quantifier iff `skolemDepth ≥ 0 && (negated && quant=ALL
|| !negated && quant=SOME)` **and** the number of enclosing universals being
skolemized-under is ≤ `skolemDepth` (`if (skolemDepth ≥ nonSkolems.size()+…)`). At
depth 0: **a top-level effective-existential** — a `some` at positive polarity, or
an `all` under negation (a `check`'s negated body) — **not nested under any
universal** — is skolemized to a **constant relation**; an existential nested under
a universal is **not** (would need a skolem *function*, depth ≥ 1). Decls' own
bound expressions are never skolemized (`visitDecl` sets depth −1). This is exactly
the polarity rule mt-038 already implemented for the *higher-order* case (§10.6);
FO extends the same `SkolemPolarity` thread to first-order decls (K3 confirms depth
0 skips the nested existential).

**Naming (exact scheme, `TranslateAlloyToKodkod.skolem` + `Skolemizer` +
`A4Solution` read-back).** The Kodkod variable for a decl `x` is named:
- inside no function: `<cmdLabel>_<var>` when `cmdLabel` is non-empty and contains
  **no** `$`; otherwise the bare `<var>` (anonymous commands have labels like
  `run$1`, which contain `$`);
- inside a function body: `<funcName>_<var>` (function's tail label) when it has no
  `$`, else bare `<var>`.

The `Skolemizer` prefixes `$` (`Relation.skolem("$" + name, …)`); at read-back
`A4Solution` strips leading `$`s and re-prefixes exactly one, uniquifying against
all names (`un.make("$" + n)`). Net Alloy-visible skolem name: **`$<cmdLabel>_<var>`**
(K1: `run foo { some x … }` → `$foo_x`), **`$<var>`** for an anonymous command
(K2: `$x`), with a uniqueness suffix on collision. A skolem relation's arity =
(number of enclosing universals skolemized-under) + the var's arity; at depth 0 for
a top-level existential that is just the var's arity (a constant). Its bound is
lower `{}`, upper = the decl bound's denotation (the same `abstract_upper` mettle
already computes for HO skolems, §10.6).

**SB-0 count effect (the reason mt-047 exists).** Because the jar enumerates the
skolem constant's assignment as part of a distinct instance, a goal with a
top-level FO existential has a **larger** SB-0 count than mettle's current
no-FO-skolem count — e.g. `run { some x: A | x=x } for 3` is jar **12** vs mettle
**7** (K4; `12 = Σ_{∅≠S⊆A} |S|`), and `oracle/test1.als`'s `check NoEmpty` is jar
**561** vs mettle **464** (§10.4). **Verdicts are always identical**; only the
count differs. Implementing FO skolemization per this section makes mettle mint the
same `$cmd_var` free relation and enumerate its witnesses, so the `skip_fo_skolem`
family (55 commands) becomes exact count matches.

This section is the input to ADR-0012's FO-skolemization decision (extend mt-038's
HO skolem machinery to top-level FO existentials).

## 16. Symmetry-breaking posture (Rung 4, mt-043)

Alloy sets Kodkod's `Options.symmetryBreaking` to an integer (default **20**) and
lets Kodkod's `SymmetryBreaker` generate **lex-leader predicates** over the
atom-permutation symmetries it detects from the bounds. **The "20" is a bound on
the length of the generated lex-leader predicate** (`SymmetryBreaker`, jar source),
a cost/completeness knob — higher breaks more symmetry (faster UNSAT, can slow
SAT), `0` disables it entirely.

**What it changes observably, and what it never changes:**
- It changes the **enumerated (SB-quotiented) instance count** at default settings
  (Y1: `some A` for 3 → 3 at SB=20, 7 at SB=0) and solve **performance**.
- It **never changes the SAT/UNSAT verdict** — a lex-leader predicate is a
  *symmetry-reducing* constraint that removes only isomorphic copies of satisfying
  assignments; it cannot make a satisfiable problem unsatisfiable or vice versa
  (argued from `SymmetryBreaker` generating predicates only over detected atom
  symmetries of the bounds; confirmed by every corpus verdict agreeing at SB-0
  where the jar ran SB=20). **`expect 1` silently forces SB=0** (§3, probe T3) —
  the harness must keep honoring that.
- Exact-bound relations (integers, `util/ordering` first/next when pinned) are
  symmetry-inert — nothing left to permute (§3, §5).

**Proposed posture (for ADR-0012 to decide).** ADR-0002's **SB=0 stays the
canonical counting yardstick** (the only regime where a count is solver-independent
and comparable, and the regime mettle's no-SB core already is). Add the Kodkod
lex-leader predicate as a **performance + parity feature** behind a dedicated
**default-symmetry (SB=20) verdict/count net** (mt-048): it needs bit-exact
lex-leader replication to match the jar's SB=20 counts, is **not** on the verdict
gate, and never touches the SB-0 counting net. This keeps the exit gate's counting
argument unchanged while giving a dedicated SB=20 comparison where the jar's
default-symmetry counts can be checked.
