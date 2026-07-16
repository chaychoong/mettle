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
  For the Rung-3 slice mettle may skip skolemization entirely and quantify
  directly (skolemization is an optimization + a nicer instance, never a verdict
  change) — see ADR-0011.

### 2.4 Integers, cardinality, `sum` — under overflow

- `#e` (cardinality) → `cset(e).count()` — a Kodkod `IntExpression`.
- `int[e]` / `sum e` (CAST2INT) → `e.sum()` — sums the integer *values* of the
  `Int` atoms in `e` (with `int[Int[x]] == x` shortcut).
- `Int[ie]` (CAST2SIGINT) → `ie.toExpression()` — the `Int` atom(s) for a value.
- `sum x: B | ie` → the Kodkod sum quantifier (mettle `IntExprKind::Sum`).
- The `fun/…` arithmetic (`plus`/`minus`/`mul`/`div`/`rem`, `IPLUS`/`IMINUS`/…)
  → the matching Kodkod `IntExpression` op (`plus`/`minus`/`multiply`/`divide`/
  `modulo`/`shl`/`shr`/`sha`). There is a peephole: `IPLUS` of `0` and `max+1`
  collapses (a `NEXT`-relation encoding detail).
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

**Draft LEDGER entry** (for the human to approve; do not implement until
`approved`):

> ### LEDGER-00N — `util/ordering` exact bounds & order pinning
> **Rule:** Opening `util/ordering[S]` forces sig `S`'s scope to be **exact**, and
> binds the order's `first`/`last`/`next` relations to **exact constants** over
> `S`'s atoms in universe order (`first = S$0`, `last = S$<n-1>`, `next` = the
> consecutive-atom successor relation) — so the linear order is fully pinned and
> the ordered atoms carry no residual symmetry, independent of the symmetry-
> breaking setting.
> **Status:** proposed. **Evidence:** probes T4/T4b (count=1 at symmetry 20 and 0;
> exact atom set `S$0..S$n-1` + private `ordering/Ord$0`). **Test:** _(added with
> the Rung-3 ordering work)_.

Rung 3's vertical slice includes `util/ordering` (it appears throughout the
corpus); the general non-enum total-order path is the one to implement first.

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

- **The general (non-enum) `util/ordering` exact-shrink** was pinned by black-box
  probe (T4/T4b: single instance, exact atom set) and by reading the
  predicate-detection + `Simplifier.shrink` path; the *precise* `next` constant
  for a >3-atom order and the interaction with a *partially* scoped ordered sig
  were not exhaustively probed. Re-derive per-case when the Rung-3 ordering bead
  lands, and file a Ledger test.
- **Skolemization** is pinned structurally (depth-0 constants, `$name` naming) but
  mettle may skip it for the Rung-3 slice (quantify directly); if kept-out, note
  in LIMITATIONS that instance skolem relations won't match the jar's shape (they
  never affect the verdict).
- **The `Simplifier` / `inferPartialInstance`** does more than the ordering shrink
  (general partial-instance inference); its full behavior was not pinned because
  it is a **performance** pass that cannot change the verdict (it only tightens
  bounds a sound solve would respect anyway). mettle may ship Rung 3 without it.
- **Integer/bitwidth fidelity beyond the overflow switch** (division/remainder
  rounding, `sum` overflow, `seq/Int` bounds) defers to Rung 4; §2.4 pins the
  switch and the two's-complement encoding, not every arithmetic corner.
- **Temporal solving** (`var`, `always`/`until`, trace scopes, the `[electrum]`
  Pardinus paths) is Rung 6; §1/§2 note where it diverges (temporal disjointness
  formulas, `maxtrace`/`mintrace`, `Prime`) but the bounded LTL→FOL expansion is
  out of scope here.
- **CNF-level count parity at default symmetry (SB=20)** is deliberately *not*
  pinned — it needs bit-exact lex-leader replication and is a later dedicated net
  (ADR-0002). Rung 3 gauges verdict + SB-0 count only.

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

Anything this document leaves ambiguous: **test against the jar first** (extend
`ProbeT`), record the answer here (verdict/count) or in SEMANTICS_LEDGER.md
(behavior), then implement.
