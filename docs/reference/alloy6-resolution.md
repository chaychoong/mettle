# Alloy 6 name resolution & type checking — pinned contract for mettle

This document pins **exactly what the reference implementation accepts, rejects,
and warns about** during name resolution and type checking — the phase that runs
*after* parsing (mt-010/011, [alloy6-grammar.md](alloy6-grammar.md)) and *before*
translation/solving. It is the **fixed contract** for Rung 2 (beads mt-017 module
graph, mt-015 stdlib, mt-018 resolver/typechecker core, mt-019 `mettle check`,
mt-020 differential gauge): implement *this*, not memory and not the public
language docs.

Provenance — all Java read at the jar's build commit
`794226dd07b536fe35c5ca44b529417183cd629b` (the pinned oracle build, ADR-0002),
under `org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/`:

- `parser/CompUtil.java` — entry points (`parseEverything_*`), recursive `open`
  loading, module-path computation, jar-stdlib fallback.
- `parser/CompModule.java` — the whole resolver: `resolveAll` orchestration,
  `Context` (bottom-up typechecker), `populate`/`resolve` (name lookup +
  candidate collection), sig/field/func/fact/assert/command registration and
  resolution, `open` handling, meta sigs.
- `parser/Macro.java` — `let`-paragraph macro substitution (depth guard).
- `ast/Type.java` — the type representation (union of products of `PrimSig`).
- `ast/ExprChoice.java` — type-directed overload disambiguation.
- `ast/Expr.java`, `ast/ExprUnary.java`, `ast/ExprBinary.java`,
  `ast/ExprList.java`, `ast/ExprCall.java`, `ast/ExprQt.java`, `ast/ExprLet.java`,
  `ast/ExprITE.java` — per-node bottom-up type rules, top-down `resolve`, and
  every relevance/redundancy warning.
- `ast/Sig.java` — builtin sigs, `PrimSig`/`SubsetSig`, field construction.
- `ast/Func.java`, `ast/Command.java`, `ast/CommandScope.java` — funcs/preds,
  commands, scopes.
- `alloy4/A4Reporter.java` — the warning/progress sink.
- `src/main/resources/models/util/*.als` — the 11 embedded stdlib modules
  (interfaces only; see §9 and the clean-room rule below).

Per PORTING_RULES (legal hygiene, ADR-0006): these files were **read to pin
behavior**; mettle is written fresh from this document, never by transcribing
Java text or class structure. For `util/*.als` this document records **only
names, signatures, and documented behavior** — never body text (neither
upstream's nor the `corpus/` copies).

Every claim a reasonable implementer could get wrong is either cited to a
specific source method/behavior or marked **jar-verified 2026-07-15** with the
probe id from §10.

---

## 0. The entry point and what "resolve" is measured against

The reference has **no parse-only public entry point**:
`CompUtil.parseEverything_fromString(rep, code)` (the function mt-013's
`ParseOnlyShim` and mt-020's gauge call) writes `code` to a temp `.als` and calls
the **3-argument** `parseEverything_fromFile(rep, null, filename)`, which:

1. canonicalizes the filename, then `parseRecursively(...)` — parse the root and
   transitively `open`ed files into `CompModule` objects (§2);
2. sets `root.seenDollar` (did any name contain `$`);
3. returns `CompModule.resolveAll(rep, root)` (§1).

Two facts a Rust implementer must not miss:

- **Resolution mode = 1** ("historical / Alloy-4.1.3" name resolution) is hard-
  wired by these entry points (`initialResolution = 1`). Mode 2 ("universal
  implicit this") exists in the code but is unreachable from the jar's public
  API. mettle implements **mode 1 only**; every `resolution == 2` branch in
  `populate` is dead for our purposes and must be omitted, not ported.
- The 3-arg path does **not** call `addGhostSig()` (only the 4-arg overload
  does). An empty model is still accepted (a `$$Default` `run` command is added
  by `addDefaultCommand`), so mettle does **not** need a ghost sig to match
  accept/reject. (jar-verified: probes 60, 61.)

**The Rung-2 gauge (mt-020) is binary: ACCEPT** (`resolveAll` returns) **vs
REJECT** (`resolveAll` throws an `Err`). **Warnings never change the verdict**
under this entry point — they are handed to `rep.warning(...)` only *after*
resolution has fully succeeded (`CompModule.java` end of `resolveAll`), and the
reporter may drop them (`A4Reporter.NOP`). So the accept/reject boundary is
"does any phase throw", and the warning taxonomy (§5.2) is a *separate*,
lower-stakes conformance target. (jar-verified: every ACCEPT probe with a `WARN`
line — 01, 40, 42.)

---

## 1. `resolveAll` — the phase pipeline (exact order)

`CompModule.resolveAll(rep, root)` runs these phases in this order. Order matters:
each phase may `throw` (→ REJECT) and later phases assume earlier ones ran. Where
a phase collects into a `JoinableList<Err> errors` instead of throwing
immediately, the throw happens at the stated checkpoint via `errors.pick()`
(which returns the **first** error — see §8 determinism).

| # | Phase | Method | Rejects (throws) on |
|---|---|---|---|
| 1 | Collect reachable modules | `getAllReachableModules` (level −1, **includes private opens**) | — |
| 2 | Bind `open` params | `resolveParams` | arg-count ≠ param-count; `none` as arg; a param sig name not found (after fixpoint) |
| 3 | Merge module instances | `resolveModules` | — (merges same file + same params) |
| 4 | Resolve sig hierarchy | `resolveSig` (per sig, memoized, recursive on parents) | parent sig not found; **cyclic inheritance** (`ErrorType`); extending a `SubsetSig` |
| 5 | Non-defined fields | `resolveFieldDecl(..., defined=false)` | duplicate field name in one sig; field bound errors (§3.4) |
| 6 | Func/pred **decls** (params + return type) | `resolveFuncDecls` → checkpoint `errors.pick()` | param/return type errors; duplicate param name |
| 7 | Defined (`=`) fields | `resolveFieldDecl(..., defined=true)` | as phase 5 |
| 8 | Meta sigs | `resolveMeta` — **only if** `Version.experimental && root.seenDollar` | — |
| 9 | Field-name clash | `rejectNameClash` | two overlapping sigs with a same-named field (`ErrorType`) |
| 10 | Func/pred **bodies**, asserts, facts (per module) | `resolveFuncBody`, `resolveAssertions`, `resolveFacts` → checkpoint `errors.pick()` | body/assert/fact type errors; fun body arity ≠ return arity; exact-param bound to variable sig |
| 11 | Commands | `resolveCommands` → `resolveCommand` | named pred/assert/sig not found; ambiguous command target; mutable non-top-level sig scoped; exact scope on variable sig |
| 12 | Emit warnings | `rep.warning(w)` for each collected `ErrorWarning` | — (never rejects) |

`Version.experimental = true` is compiled into the pinned jar (grammar-doc §0),
so phase 8 runs whenever any `$` name appeared. `metaSig`/`metaField` (`sig$`,
`field$`) and the `static$`/`var$` subset sigs are synthesized here; a plain
model with no `$` skips it entirely. (jar-verified: `some sig$` accepted, probe
44.)

---

## 2. Module system and `open`

### 2.1 File search order (`CompUtil.parseRecursively` + `computeModulePath`)

For an `open X` whose relative module path is `x.filename` (no `.als`), inside a
parent file `filename` with declared module name `u.getModuleName()`, the
content is resolved by trying, in this exact order (first hit wins):

1. `computeModulePath(parentModuleName, parentFile, x.filename)` looked up in the
   pre-fetch cache `fc`, then in `loaded`. `computeModulePath` walks the parent's
   *declared module name* and the target path segment-by-segment; on the first
   mismatch (or when either runs out of segments) it returns
   `up(parentFile, slashCount+1)/<target with '/'→sep>.als` — i.e. **relative to
   the directory the parent resolved from**, adjusted by how deep the parent's
   own module path was.
2. `x.filename` verbatim in `fc`, then in `loaded`.
3. `Util.readAll(cp)` from disk (the path from step 1).
4. the same path with `.als` → `.md` (Markdown-literate models).
5. **jar-embedded fallback**: `Util.jarPrefix() + "models/" + x.filename + ".als"`
   — this is how the 11 `util/*` modules (and the book/example models) are found
   when not on disk.

Implication for mettle: the embedded stdlib (mt-015) is the **last** fallback; a
same-named file next to the user's model *shadows* it. mettle bundles its
clean-room `util/*` as resource #5.

### 2.2 Module path → file mapping; cycles

`open` targets are relative module paths (`util/ordering`, `a/b/c`). Cycle
detection is by **filename appearing twice on the current open-chain**
(`thispath`, a `LinkedHashSet`): a repeat throws `ErrorSyntax` "Circular
dependency in module import…" — this is decided at *load* time, before
`resolveAll`. Parametric instantiation does not change the file, so the same file
opened with different args still counts as the same node for cycle purposes.

### 2.3 Parametric opens and instantiation (`resolveParams`, `resolveModules`)

- An `open util/ordering[Elem]` supplies positional args; `resolveParams` binds
  each of the imported module's params (declared `module util/ordering[exactly
  elem]`) to a sig looked up **in the opening module** via `getRawSIG`. This runs
  as a **fixpoint** (a param may itself be another param not yet bound); it
  terminates when nothing changes. Rejects: `arg-count ≠ param-count` (probe 31),
  `none` as an arg (probe 64), a still-unresolved arg name after the fixpoint.
- **Instance identity** (`resolveModules`): two `CompModule`s are merged iff they
  have the **same source filename AND equal `params` maps** (`params.equals`).
  So `open util/ordering[A]` written twice is a single instance; `open
  util/ordering[A]` and `open util/ordering[B]` are two distinct instances.
  (jar-verified: probes 24, 25.) When merged, the survivor is chosen by a
  `$`-in-path / `slashComparator` tiebreak (determinism note §8).

### 2.4 Aliases (`as`), qualified lookup, and auto-aliasing

`addOpen` computes the alias:

- explicit `as name` → that name (rejects `$`, `@`, `/` in the alias);
- else if there are **no** args and the filename is a plain identifier run, the
  alias is the filename itself;
- else a placeholder `open$N`. `doneParsing` then rewrites each `open$N` whose
  filename's **basename** is a legal identifier and unused to that basename.

So `open util/ordering[Color]` (no `as`) ends up aliased **`ordering`**, and the
funcs are reachable as `ordering/first` or bare `first` — **not** `Color/first`.
(jar-verified: probe 09 rejects `Color/first`; probes 20, 21 accept `first` and
`ordering/first`.)

Two opens that resolve to the **same alias but different (file,args)** →
`ErrorSyntax` "You cannot import two different modules using the same alias"
(probe 26). Two opens with identical (alias, file, args) are silently allowed
(the `util/sequniv`-as-`seq` case relies on this).

Qualified name lookup (`getRawQS`): split on `/`; walk `opens.get(alias)` down
the module chain (a `private` open blocks the hop when `level>0`); at the tail,
look up sig/assert/func in that module. `this/` and a leading module-self prefix
are stripped by `Util.tailThis`. If a qualified lookup finds nothing at the tail,
it **falls back to an unqualified search from the current module** (`getRawNQS`).

### 2.5 `private`, module header, `$`

- `private open`/`private sig`/`private fun`… are legal (probe 27 accepts a
  single-file `private sig`). `private` only bites **across** modules:
  `getRawNQS`/`getRawQS` skip a private member unless the querying module *is*
  the defining module. Private opens are still reachable for `getAllReachable`
  (level −1) but hidden from `getAllNameable` (level ≥ 1).
- `module` header: must be the first paragraph (`addModelName` throws if
  `status>0`); at most once. The **root** module's declared name is *not* checked
  against its filename — `module totallyDifferentName` in a file of another name
  is accepted (probe 11, probe 62 shows header-not-first rejected). (These are
  parse-phase/`CUP` checks that mt-013 already classified as SYNTAX; listed here
  for completeness.)
- Any `$` in a *declared* name is a parse-time `ErrorSyntax` from the `nod()`
  grammar action (probe 63) — SYNTAX, covered by mt-013. But `sig$`/`field$` are
  the reserved meta names, reachable only via the meta machinery (§1 phase 8).

---

## 3. Top-level registration and resolution

### 3.1 Sigs (`addSig`, `resolveSig`)

- Quals stack into `Attr`s: `abstract`, `var`, `private`, one of `lone/one/some`.
  A subset sig carries `Attr.SUBSET`; `extends` yields `Attr.SUBSIG`; `in`/`=`
  yield `SUBSET`, with `=` additionally `Attr.EXACT` (`SigParent::Eq`).
- Parent kind: `PrimSig` for `extends` (single parent, default `UNIV`);
  `SubsetSig` for `in`/`=` (a *list* of parents — subset sigs may have multiple).
  (jar-verified: `sig C in A + B {}` accepted, probe 29.)
- `resolveSig` is memoized (`new2old`) and recursive: it resolves each parent
  first, so it topologically orders the DAG and detects **cyclic inheritance**
  (`topo` set) → `ErrorType` (probe 07). Extending a `SubsetSig` →
  `ErrorSyntax` "A signature can only extend a toplevel signature or a
  subsignature." A parent name not found → `ErrorSyntax` "The sig … cannot be
  found."
- `resolveSig` also emits (non-fatal) **var/static warnings**: static sig inside
  a variable subset parent; static sig extends variable sig; `var` redundant
  because parent is static.
- Duplicate **sig** name in a module → `ErrorSyntax` from `dup` (probe 05).
  `dup` also rejects empty names, `@`, `/`, and the reserved names
  `univ`/`Int`/`none` as declared sig names.
- Sig `type()` is the sig itself as a unary `PrimSig` (`Sig extends Expr`); a
  field's type is `sig.type.product(bound.type)` (§3.4).

### 3.2 Enums (`addEnum`) — exact desugaring

`enum N { A, B, C }` desugars (at parse time, in `addEnum`) to, in order:

1. `abstract private?-inherited sig N {}` with `Attr.ENUM` (and `WHERE`/pos of
   `N`);
2. one `one sig A extends N {}`, `one sig B extends N {}`, … (in listed order);
3. `open util/ordering[N]` (no alias → auto-aliased `ordering`, §2.4).

Empty enum `enum N {}` → `ErrorSyntax` "Enumeration must contain at least one
name" (`addEnum`; parse-phase, SYNTAX). The ordering funcs (`first`, `next`,
`prev`, `min`, `max`, …) become available for the enum via the auto-alias.
(jar-verified: probes 09, 20, 21.)

### 3.3 Facts, sig facts, and **implicit `this`** (`addFact`, `resolveFacts`)

- Free-standing `fact [name|"string"] { … }` → appended to `facts` (a `List`,
  keyed by name only for reporting). **Duplicate fact names are NOT rejected**
  (probe 67) — unlike sigs/asserts. Anonymous facts get synthetic names
  `fact$N`.
- Each fact body is typechecked with a fresh `Context` and `resolve_as_formula`.
- **Sig appended facts** (`sig A {…} { <fact> }`): resolved in `resolveFacts`
  with `cx.rootsig = s` and a `this` binding injected into the env:
  - if the sig is **not** `one`: `cx.put("this", s.decl.get())` — `this` is a
    fresh variable ranging over `one s`;
  - if the sig **is** `one`: `cx.put("this", s)` — `this` *is* the singleton sig.

  This is the precise implicit-`this` rule: inside a sig fact (and a field bound,
  §3.4), a bare field name `f` of this sig resolves to `this.f` (in `populate`,
  resolution-1 branch: when `rootsig.isSameOrDescendentOf(f.sig)` and the name is
  not `@`-prefixed, the candidate is `THIS.join(field)`). A field of *another*
  sig resolves to the bare relation (penalty-weighted). At **top level** (no
  rootsig) there is **no** implicit `this`: a bare field name is the whole binary
  relation `sig <: f`, so `some f` at top level is accepted and means "the
  relation is non-empty" (probe 14). (jar-verified: probes 22, 23, 14.)
- `@f` suppresses the implicit-`this` join (the leading `@` is stripped in
  `populate` and disables the `THIS.join` candidate).

### 3.4 Fields (`resolveFieldDecl`, `Sig.addTrickyField`/`addDefinedField`)

- Non-defined field `f: e`: bound `e` is typechecked with `this` bound to
  `s.decl.get()` and `cx.rootfield = d`. Multiplicity default: a bare unary bound
  becomes `one` of it (`ExprUnary.Op.ONEOF`); `some/lone/one e` set the marker;
  `set e`/`seq e` stay as-is. Field type = `sig.type.product(bound.type)`.
- Defined field `f = e` (`ExprUnary.Op.EXACTLYOF`): resolved in the **later**
  defined-field pass (phase 7), so a defined field may reference other fields.
- Field bound rejects (`Sig.Field` constructor): builtin sig cannot have fields;
  a **non-defined** bound cannot contain a fun/pred call ("Field … declaration
  cannot contain a function or predicate call"); a bound that is a non-empty
  arity but all-`none` ("Cannot bind field … to the empty set or empty
  relation").
- Field name scoping in `populate`: a field is visible to bounds of the same sig
  or a descendant; referencing an ancestor sig's field is allowed, a cross-branch
  field gets a weight penalty. A field decl may **not** call funcs/preds (the
  `fun` flag in `populate` excludes funcs when `rootsig != null && rootfield`
  non-`EXACTLYOF`).
- **Field-name clash across overlapping sigs** (`rejectNameClash`, phase 9):
  two fields with the same label whose owner sigs' first type-columns overlap →
  `ErrorType` (probe 06). Disjoint sigs may reuse a field name.
- `disj f, g: e` (left `disj`) marks the named fields mutually disjoint;
  `f: disj e` (right `disj`, `is_bound_disj`) is separate. `disj` + `=` is a
  parse error (grammar-doc §4.4).

### 3.5 Funcs and preds (`addFunc`, `resolveFuncDecls`, `resolveFuncBody`)

- `pred`/`fun` are **overload sets**: `funcs` maps a name to a `List<Func>`.
  Declaring two preds/funs with the same name is **accepted** at declaration
  (probe 68); ambiguity is only decided at *call sites* (§4.4). Contrast asserts
  and macros, which reject duplicates.
- A receiver `sig.pred[...]`/`sig.fun[...]` prepends a `this: sig` param (as
  `Decl` index 0). Receiver may be a builtin sig (`fun String.cat[...]`).
- Params: each `Decl` resolved left-to-right; a param may reference earlier
  params and any visible sig/field but **not** call funcs/preds
  (`cx.rootfunparam = true`). Duplicate param name → `ErrorSyntax`. A param decl
  may not be `private` or bound to a `disj` (right-disjoint) expression.
- Return decl (`fun` only): `resolve_as_set`; a bare unary return → `one` of it;
  cannot contain calls or temporal ops (`Func` constructor).
- Body (phase 10): pred body `resolve_as_formula`; fun body `resolve_as_set`,
  then `setBody` enforces **body arity == return-decl arity** (`ErrorType`, probe
  35). A non-fatal **warning** fires if the body's tuple type is disjoint from
  the declared return type.
- **Recursion is NOT rejected** at resolve time: `pred p[a]{ p[a] }` is accepted
  (probe 12); only *macro* substitution has a depth guard (§3.7). (Recursion
  limits, if any, are a translator concern for later rungs.)

### 3.6 Assertions and commands (`addAssertion`, `resolveCommand`)

- `assert [name|"string"] { … }` → `asserts` map; **duplicate assert name
  rejected** (`ErrorSyntax`). Anonymous → `assert$N`. Body stored NOOP-wrapped,
  resolved `as_formula` in phase 10.
- Commands (`run`/`check`) resolve their target in `resolveCommand` (phase 11):
  - `check name`: look up an **assertion** (`getRawQS(2,…)`, fallback
    `getRawNQS`); missing → "The assertion … cannot be found" (probe 33);
    the command formula becomes `assertBody.not()`.
  - `run name`: look up a **pred/fun** (`getRawQS(4,…)`); missing → "The
    predicate/function … cannot be found" (probe 32); for a fun the formula is
    `body in returnDecl`, and params are existentially quantified
    (`some decls | …`).
  - `run {block}` / `check {block}`: anonymous — `addCommand` synthesizes a
    `run$N` pred / `check$N` assert from the block.
  - `>1` matching target → ambiguous (`unique` → `ErrorSyntax`).
- **Scopes** (`CommandScope`, resolved in `resolveCommand`): each scope's sig is
  looked up (`getRawSIG`); missing → "The sig … cannot be found" (probe 34).
  Additional resolve-time rejects (the checks mt-013's LIMITATIONS deferred):
  - a **mutable, non-top-level** sig given a scope → `ErrorSyntax` "Mutable sig …
    is not top-level thus cannot have scopes assigned.";
  - an **exact** scope on a **variable** sig → `ErrorSyntax` "… is variable thus
    scope cannot be exact."
  - `CommandScope` constructor invariants: `endingScope ≥ startingScope ≥ 0`,
    `increment ≥ 1`; `startingScope == endingScope` forces `increment = 1`.
  - `expect N` is normalized to `-1/0/1` (any positive → 1); other values do not
    reject (grammar-doc §4.5). Growing/exact-on-`int`/`Int`/`seq` and
    scope-on-`univ`/`none` are **parse-phase** `CUP` checks (SYNTAX, mt-013).
- Command follow-up chaining (`cmd => run …`, `is_followup`): the follow-up
  replaces its parent in the `commands` list and carries a `parent` pointer.

### 3.7 Macros (`let` paragraphs, `Macro`)

- Top-level `let name[params] = expr | { … }` registers a `Macro`. **Duplicate
  macro name rejected** (`ErrorSyntax`); duplicate param name rejected.
- A macro reference expands by textual substitution during typechecking
  (`Context.visit(ExprVar)`/`visit(ExprBadJoin)`), decrementing an `unrolls`
  budget that starts at **20**; exhaustion → `ErrorType` "Macro substitution too
  deep; possibly indicating an infinite recursion." (`Macro.java`). This is the
  only recursion guard in resolution. (jar-verified: probe 43 accepts a simple
  macro.)

---

## 4. The type system

### 4.1 `Type` representation (`ast/Type.java`)

A `Type` is: a boolean `is_bool` flag + a **union of `ProductType` entries**,
where each `ProductType` is a `PrimSig[]` (arity = array length). Plus an
`arities` **bitmask** (`1<<k` set iff an entry of arity `k≤30` exists; bit 0 iff
some arity `>30`). Notable constants and rules:

- `EMPTY` (no entries, `is_bool=false`) is the **error/ill-typed** type:
  invariant `type == EMPTY iff errors nonempty` (`Expr`).
- `FORMULA` (no entries, `is_bool=true`) is the boolean/formula type.
- `is_int()` is **computed**, not stored: true iff some entry is the **unary**
  `SIGINT`. `smallIntType()` is the special "primitive int" `{Int}` with an
  `is_small_int` marker used to distinguish a computed int expression from the
  `Int` sig relation.
- Builtin unary sigs: `UNIV`, `SIGINT`(`Int`), `SEQIDX`(`seq/Int`, child of
  `Int`), `STRING`, `NONE`. `NONE` is the empty-tuple absorbing element:
  `NONE->X == NONE->NONE`; a product/join touching `NONE` collapses.
- `iden` is `ExprConstant.Op.IDEN` (type `univ->univ`, arity 2). `univ`/`none`
  are the top/bottom unary sigs. `String`, `seq/Int` are ordinary builtin sigs.
- **Subsumption**: adding an entry `x` drops any existing entry that is a subtype
  of `x` (same arity), and skips `x` if it is subsumed — so a `Type` keeps only
  maximal products per arity (`Type.add`). Subtype on products is pointwise
  `isSameOrDescendentOf`.
- **Fold**: for display and `isSubtypeOf`, a set of products differing in one
  column that together exhaust an *abstract* parent's children is folded back to
  the parent. This is presentation/subtype-only — bounding types are the unfolded
  union.

### 4.2 Bottom-up bounding types (`Context` + each node's `Op.make`)

`Context` (a `VisitReturn<Expr>` in `CompModule`) walks the parsed, still-
ambiguous `Expr` tree and rebuilds it with types computed **bottom-up**: every
constructor `Op.make(...)` computes the node's `Type` from its children's types
and attaches any `ErrorType`. Representative rules (all from `ExprUnary`/
`ExprBinary`/`ExprList`):

- Set ops: `+`/`&`/`-`/`++` require **common arity** (else `ErrorType`
  "… can be used only between 2 expressions of the same arity …"); `union` =
  `unionWithCommonArity`, `intersect` = pointwise, `-` (MINUS) keeps the left
  arity, `++` = `unionWithCommonArity` and needs same arity.
- `->` (product): type = `left.product(right)`, arities add; the 16 arrow
  multiplicities carry `mult` flags (a `mult`-tagged operand where a plain set is
  required → `ErrorSyntax` "Multiplicity expression not allowed here").
- `.` (join): type = `left.join(right)` (arity `a+b-2`, drops when the touching
  columns are disjoint). If the join type is `EMPTY` the node becomes an
  `ExprBadJoin`, which is *deferred* (it may still succeed as a call — see §4.4).
- `<:`/`:>` domain/range restrict; `~` transpose (binary only); `^`/`*`
  transitive/reflexive-transitive closure (binary only; `*` yields `univ->univ`).
- Comparisons `= != in !in < > =< >= …`: type `FORMULA` when well-formed. `=`/`!=`
  need **common arity OR both `is_int`** (else `ErrorType`, probe 13). `in`/`!in`
  need common arity. Arithmetic comparisons (`<`,`>`,`=<`,`>=`, `<<`,`>>`,`>>>`)
  `typecheck_as_int` both sides.
- `#` cardinality, `sum`/`int` casts → `smallIntType`; the integer binops
  `fun/add` `fun/sub` `fun/mul` `fun/div` `fun/rem` (a.k.a. `IPLUS/IMINUS/MUL/
  DIV/REM`) → `smallIntType`, both sides `typecheck_as_int`.
- Quantifiers (`ExprQt`): each decl bound `resolve_as_set`, a bare unary decl
  bound becomes `one` of it; body `resolve_as_formula` (or `resolve_as_int` for
  `sum`). Unused decl var → **warning** "This variable is unused."
- `let` (`ExprLet`): binds the resolved RHS type; unused → warning.
- `if/else` (`ExprITE`): cond `as_formula`; redundant-branch warnings.
- Conjunction/disjunction are n-ary `ExprList` (`AND`/`OR`); `disj[…]` →
  `ExprList.Op.DISJOINT`; `pred/totalOrder[…]` → `ExprList.Op.TOTALORDER`.

### 4.3 Top-down resolution (`Expr.resolve(t, warns)`)

After bottom-up typing, each `resolve_as_{formula,int,set}` does
**typecheck → resolve(relevantType) → typecheck**:

- `resolve_as_formula` = `typecheck_as_formula` (must be `is_bool`) →
  `resolve(FORMULA)` → `typecheck_as_formula`.
- `resolve_as_int` = `typecheck_as_int` → `resolve(smallIntType)` →
  `typecheck_as_int`. `typecheck_as_int` accepts a `small_int` as-is, casts an
  `is_int` relation via `CAST2INT`, else errors.
- `resolve_as_set` = `typecheck_as_set` (a `small_int` is cast to `Int` via
  `CAST2SIGINT`; an `is_int` relation stays) → `resolve(removesBoolAndInt(type))`
  → `typecheck_as_set`.

`resolve(t, warns)` pushes the **relevant type** `t` down: each node computes the
relevant type for each child (e.g. for `a in b`, both children get the
intersection/common-arity slice; for join, the child slices are recomputed from
`t`), recurses, and — crucially — this is where **relevance/redundancy
warnings** are emitted (§5.2) and where **ExprChoice** nodes are disambiguated.

### 4.4 Overload disambiguation (`ExprChoice.resolveHelper`)

Ambiguous names/joins are `ExprChoice { choices: [Expr], reasons: [String] }`
built bottom-up by `populate`/`process`. `resolve(t, warns)` picks:

1. **Exact matches**: choices whose type `intersects(t)` (or both `is_bool`).
2. Else **legal matches**: choices with `hasCommonArity(t)`.
3. If `>1`, keep only the **minimum-weight** choices (weight penalizes
   implicit-`this` joins and cross-branch field refs — the "penalty of 1" in
   `populate`).
4. If still `>1` **on the first pass**: fully `resolve` each candidate against
   `t` and retry once (`firstPass=false`).
5. Exactly 1 → resolve it.
6. `>1` but **all collapse to the same-arity empty set** → return `none` (of that
   arity). This is why genuinely-empty ambiguities don't error.
7. Otherwise → `ErrorType`: either "This name is ambiguous due to multiple
   matches:" + reasons (probe 15) or "This name cannot be resolved; its relevant
   type does not intersect …".

**Candidate collection scope chain** (`Context.resolve` → `populate`), in order:

1. **Qualified prefix** `a/b/name`: resolve macros then walk `opens` down the
   module chain (private opens block cross-module hops); at the tail do a normal
   lookup.
2. **Local env** `env.get(name)` — let/quantifier vars and fun params and `this`
   (lexical, innermost wins).
3. **Macros** across all *nameable* modules — multiple macros same name →
   `ErrorType` "There are multiple macros with the same name".
4. **Globals** (`addGlobal`).
5. **Builtins**: `univ Int seq/Int String none iden sig$ field$`.
6. **`populate`**: sigs + params (`getRawNQS`/`getRawQS`), funcs/preds (as
   `ExprCall` if 0 args else `ExprBadCall` awaiting args), and — inside a sig
   context — the implicit-`this` first-argument candidate and the implicit-`this`
   field join; then **fields** by label across nameable modules (private-filtered);
   then meta-sig/meta-field fields.

A function-application `f[args]` (box join) is realized by `Context.process`:
each `ExprBadCall` in the left/right choice list is completed with the next arg
and promoted to `ExprCall` when the accumulated args are `applicable` (arity +
type-intersection check per param), else falls back to a real relational join.
This is why `f(x)` vs `f[x]` and "is it a call or a join" are resolved by *type*,
not syntax — the classic Alloy overload behavior. A fully-failed call yields
"Name cannot be resolved; possible incorrect function/predicate call; perhaps you
used ( ) when you should have used [ ]".

### 4.5 Integers, `seq/Int`, `String` — what 6.2.0 actually does

**There is no automatic `int`↔`Int` coercion.** The historical `INT2SIGINT`/
`SIGINT2INT` casts are commented out (`[AM]` blocks in `Type`, `ExprBinary`,
`ExprChoice`). Consequences a Rust implementer must reproduce exactly:

- `+ - = != in` etc. are **purely relational**. `1 + 2` is the **set `{1,2}`**,
  not `3`: `#(1+2) == 2` (jar-verified, probe 03). Integer arithmetic is only via
  the `fun/…` binops (`plus`/`minus`/`mul`/`div`/`rem`, `fun/add`…) or `util/
  integer` (probe 04).
- `=`/`!=` succeed when both sides are `is_int` even at different "arities": a
  field of declared type `Int` has an `is_int()` relational type, and an int
  literal is `small_int`, so `a.n = 1` type-checks as `FORMULA` (probe 02).
- The manual `Int[e]` cast is the `ExprBadJoin`/`ExprBinary` special case
  `left.type().is_int() && right.isSame(SIGINT)` → returns `left` (the int),
  i.e. `Int[e]` casts an int expr to the `Int` sig atom. `int[e]`/`sum e` cast a
  unary set of `Int` atoms to a primitive int (`CAST2INT`); `#e` is cardinality.
- `seq/Int` is `SEQIDX`, a child sig of `Int`; the `seq` keyword on a field opens
  `util/sequniv` (aliased `seq`) via `addSeq` and desugars to an `Int->elem`
  relation with `isSeq` constraints (probe 10).
- `String` is a builtin sig; string literals are atoms of `String` (experimental
  on). No special typing beyond membership (probe 28).

### 4.6 Temporal (Rung 2 scope)

`var` sigs/fields, `'` (prime), and the unary/binary temporal ops
(`always eventually after before historically once`; `until releases since
triggered`) **resolve and type-check** in Rung 2 exactly like their static
counterparts (prime is a NOOP-typed postfix; temporal binaries are `FORMULA`).
They are not *solvable* until a later rung (STYLE T2 — a typed "parsed, not yet
solvable" error), but that boundary is downstream of resolveAll; the accept/
reject verdict for a well-typed temporal model is ACCEPT.

---

## 5. Errors vs warnings — the exact taxonomy

### 5.1 What `resolveAll` REJECTS (throws `Err`)

Every reject observed/derived, with the throwing method (the mt-020 gauge only
needs ACCEPT vs REJECT; the method column supports triage):

| Reject | Method | `Err` kind | Probe |
|---|---|---|---|
| open arg-count ≠ params | `resolveParams` | ErrorSyntax | 31 |
| `none` as open arg | `resolveParams` | ErrorSyntax | 64 |
| open param sig not found | `resolveParams` | ErrorSyntax | — |
| two modules, same alias | `addOpen` | ErrorSyntax | 26 |
| circular module import | `parseRecursively` (load) | ErrorSyntax | — |
| duplicate sig/param name | `dup` | ErrorSyntax | 05 |
| cyclic sig inheritance | `resolveSig` | ErrorType | 07 |
| parent sig not found | `resolveSig` | ErrorSyntax | — |
| extends a subset sig | `resolveSig` | ErrorSyntax | — |
| duplicate field in one sig | `resolveFieldDecl` | ErrorSyntax | — |
| field bound has a call (non-defined) | `Sig.Field` | ErrorSyntax | — |
| field bound to empty relation | `Sig.Field` | ErrorType | — |
| overlapping sigs, same field name | `rejectNameClash` | ErrorType | 06 |
| unknown name in expr | `hint` | ErrorSyntax | 08, 09 |
| arity mismatch (`= + & in` …) | `ExprBinary.error` | ErrorType | 13 |
| ambiguous name / call | `ExprChoice.resolveHelper` | ErrorType | 15 |
| type does not intersect any candidate | `ExprChoice.resolveHelper` | ErrorType | — |
| fun body arity ≠ return arity | `Func.setBody` | ErrorType | 35 |
| duplicate assert/macro name | `addAssertion`/`addMacro` | ErrorSyntax | — |
| macro expansion too deep (>20) | `Macro` | ErrorType | — |
| command target (pred/assert) not found | `resolveCommand` | ErrorSyntax | 32, 33 |
| scope sig not found | `resolveCommand` | ErrorSyntax | 34 |
| mutable non-top-level sig scoped | `resolveCommand` | ErrorSyntax | — |
| exact scope on variable sig | `resolveCommand` | ErrorSyntax | — |
| exact param bound to variable sig | `resolveAll` phase 10 | ErrorSyntax | — |

`errors.pick()` throws the **first** error in `JoinableList` order (§8). Multiple
independent errors in one model surface one at a time.

### 5.2 What `resolveAll` WARNS about (never fatal under `parseEverything`)

Warnings are collected into a `List<ErrorWarning>` and emitted only after
success. Under `A4Reporter.NOP` they vanish; under a capturing reporter they
appear **in collection order** (see §8). Full catalog (message stems):

- **Relevance / redundancy** (`ExprUnary`/`ExprBinary`, only when `warns != null`
  and the relevant type shows the subexpression cannot contribute):
  - `~`/`^`/`*` "… is redundant since its domain and range are disjoint";
    "The value of this expression does not contribute to the value of the parent";
  - `= !=` "== is redundant, because the left and right expressions are always
    disjoint / always have the same value";
  - `in !in` "Subset operator is redundant, because … always empty / disjoint /
    same value";
  - `&` "& is irrelevant because the two subexpressions are always disjoint"
    (probes 01, 42);
  - `+ ++ - <: :> .` "… is irrelevant since … subexpression is redundant" /
    "The join operation here always yields an empty set";
  - `int[]` "This expression should contain Int atoms".
- **Unused binder**: `all/some/…`/`let` "This variable is unused" (probe 40).
- **Redundant ITE branch**: "This subexpression is redundant."
- **Implicit conjunction**: "Implicit in-line conjunction between two formulas"
  (from `ExprList.implicits`; fires only where the parser tagged an implicit
  `&&`, not for every blank-line-separated formula — probe 42 did *not* trigger
  it).
- **Static/variable mismatches** (`resolveSig`, `resolveFieldDecl`): static sig
  in variable parent; static/var extends mismatch; static field in variable sig;
  static field with variable bound.
- **Function return disjoint**: "Function return value is disjoint from its
  return type."
- `Sig.java` "Undefined case …" is an internal `ErrorWarning` not reachable from
  well-formed input.

### 5.3 Fatal-warning modes

`parseEverything_fromString`/`_fromFile` never treat warnings as fatal — the
reject set is exactly §5.1. (The interactive Analyzer has a
"warnings are fatal" preference in its `SimpleReporter`, but that is GUI/solve
configuration, not part of `resolveAll`, and is out of scope for the mt-020
gauge, which drives `resolveAll` directly.) **mettle's `mettle check` (mt-019)
mirrors the `resolveAll` verdict: warnings are reported, never rejected.**

---

## 6. Gotchas / dark corners (verify against the jar before implementing)

1. **`+` is set union on ints.** `1+2` is `{1,2}`; only `fun/…`/`util/integer`
   add. (probe 03) — the single most common false expectation.
2. **No `int`↔`Int` coercion in 6.2.0** (§4.5). Every historical coercion path is
   dead code. Do not resurrect it.
3. **Resolution mode 2 is dead** from the public API. Implement mode 1 only; the
   `resolution == 2` branches in `populate` never run for us.
4. **No ghost sig via the string entry point.** Empty models accept without one
   (probes 60, 61).
5. **Implicit `this` only inside a sig context.** Top-level bare field name = the
   whole relation; `some f` at top level is accepted (probe 14). `@f` disables
   the implicit join.
6. **Enum has no `EnumName/` namespace.** Its ordering is auto-aliased
   `ordering` (probes 09, 20, 21).
7. **Duplicate names split by kind.** Sigs/asserts/macros/params reject dups;
   **funcs/preds overload** (probe 68); **facts don't check names at all** (probe
   67).
8. **Instance identity = filename + equal params** (`resolveModules`), not alias
   and not textual open. Two `open util/ordering[A]` are one instance; `[A]` vs
   `[B]` are two (probes 24, 25).
9. **Root module name is unchecked** against filename (probes 11, 62). Only
   *submodule* resolution uses the declared name (`computeModulePath`).
10. **Recursion is not a resolve error** (probe 12); only macros are depth-
    limited (20).
11. **`ExprBadJoin` is not immediately an error** — it may still become a valid
    call in `process`. Don't reject on a failed relational join before trying the
    call interpretation.
12. **`seenDollar` gates a whole phase.** A stray `$` (only reachable via the
    meta `sig$`/`field$` names since declared `$` names are rejected earlier)
    turns on meta-sig synthesis, adding `sig$`, `field$`, `static$`, `var$` and
    extra facts.

---

## 7. `util/*` module interfaces (clean-room reference for mt-015)

The 11 modules the jar embeds under `models/util/`, with **public interface
only** (module header + params + exported sig/field/fun/pred/assert/macro
*signatures*). **Bodies are deliberately omitted** (ADR-0006 clean-room rule):
mt-015 writes mettle's own bodies from these signatures + Ledger-pinned behavior,
never from upstream text. Signatures are not copyrightable and *must* match for
conformance — an argument-order, arity, param-name, or result-multiplicity
mismatch is a conformance bug (a user model that calls the stdlib will resolve
differently). §7.1–§7.11 below are the precise per-member appendix (this
supersedes the condensed listing that shipped with mt-016; the corrections it
forced are in the mt-016 follow-up report).

**Notation** (our own, not verbatim source): `f(p: T, …): R` is a fun with
params `p: T` and result type `R`; `pred p(p: T, …)` is a pred; `()` marks a
0-ary member. Types carry an explicit multiplicity keyword: `one X`, `lone X`,
`set X`, `X -> Y` (product, default arrow mult), `X -> lone Y`, etc. A **bare
unary** result/param declared without a keyword (`: elem`, `: Int`, `: node`,
`: Bool`, `: SeqIdx`) has effective multiplicity **`one`** (the decl-default
oneOf rule, §3.4/§3.5) — flagged `⟨one⟩` where it could mislead. Param **names
are part of the interface** (they are visible in reasons/errors and, for
`this.`-style calls, in resolution) — reproduce them verbatim. `[private]` marks
a hidden member; a private member's *name* must still be hidden by mettle's
rewrite (it must not leak into the module's public namespace).

### 7.1 `util/ordering[exactly elem]`

Single linear order over `elem`; **param `elem` is `exactly`-marked** (forces the
instance's scope to be exact — analyzer special-casing, below).

- Internal sig: `private one sig Ord { First: set elem, Next: elem -> elem }`
  with appended fact `pred/totalOrder[elem, First, Next]`. The `pred/totalOrder`
  **builtin** is called with **3 args in order (domain, first-set, next-rel)**:
  arg1 = the ordered domain `elem`, arg2 = `Ord.First` (type `set elem`),
  arg3 = `Ord.Next` (type `elem -> elem`). `First`/`Next` are `Ord`'s **fields**
  (referenced by implicit `this` inside `Ord`'s appended fact). `Ord` and its two
  fields are **private** (the `Ord` name and `First`/`Next` are not part of the
  callable surface; users go through the funcs/preds).
- Funcs/preds (all callable, no receiver):
  - `first(): one elem` ⟨explicit `one`⟩ · `last(): one elem`
  - `prev(): elem -> elem` · `next(): elem -> elem`  ⟨0-ary, binary result⟩
  - `prevs(e: elem): set elem` · `nexts(e: elem): set elem`
  - `pred lt(e1: elem, e2: elem)` · `pred gt(e1, e2: elem)` ·
    `pred lte(e1, e2: elem)` · `pred gte(e1, e2: elem)`
  - `larger(e1: elem, e2: elem): elem` ⟨one⟩ · `smaller(e1: elem, e2: elem): elem`
  - `max(es: set elem): lone elem` · `min(es: set elem): lone elem`
- Public assertion: `assert correct`. The module also declares its own
  `run {}`/`check correct` commands (self-test) — not part of the callable API but
  present in the parsed module.
- **Analyzer special-casing** (Java, not `.als`): the `exactly` param + `Ord`
  private singleton let the solver pin exact bounds and break symmetry on the
  ordered sig. mt-015/mt-017 reproduce this as SEMANTICS_LEDGER-pinned behavior,
  independent of whose `.als` ships.

### 7.2 `util/integer` (no params)

Special-cased by name in the resolver (`Context.isIntsNotUsed`,
`getAllReachableUserDefinedFunc` skip `"util/integer"`). All members take/return
`Int` (the sig), never primitive int:

- `add(n1: Int, n2: Int): Int` · `plus(n1, n2: Int): Int` ·
  `sub(n1, n2: Int): Int` · `minus(n1, n2: Int): Int` · `mul(n1, n2: Int): Int` ·
  `div(n1, n2: Int): Int` · `rem(n1, n2: Int): Int`
- `negate(n: Int): Int`  ⟨**unary** — one param⟩
- `pred eq(n1, n2: Int)` · `pred gt(n1, n2: Int)` · `pred lt(n1, n2: Int)` ·
  `pred gte(n1, n2: Int)` · `pred lte(n1, n2: Int)`
- `pred zero(n: Int)` · `pred pos(n: Int)` · `pred neg(n: Int)` ·
  `pred nonpos(n: Int)` · `pred nonneg(n: Int)`
- `signum(n: Int): Int`  ⟨unary⟩
- `int2elem(i: Int, next: univ -> univ, s: set univ): lone s`  ⟨**3 params in
  order (i, next, s)**; result is `lone s`, i.e. lone of the *supplied set param*⟩
- `elem2int(e: univ, next: univ -> univ): lone Int`  ⟨**2 params only** (e, next);
  no set param; result `lone Int`⟩
- `max(): one Int` · `min(): one Int`  ⟨**0-ary** overloads⟩
- `next(): Int -> Int` · `prev(): Int -> Int`  ⟨0-ary, binary result; **no
  set-form of next/prev**⟩
- `max(es: set Int): lone Int` · `min(es: set Int): lone Int`  ⟨set overloads —
  `max`/`min` are each an overload set of the 0-ary and the set form⟩
- `prevs(e: Int): set Int` · `nexts(e: Int): set Int`
- `larger(e1: Int, e2: Int): Int` · `smaller(e1: Int, e2: Int): Int`

### 7.3 `util/boolean` (no params)

- `abstract sig Bool {}`
- `one sig True extends Bool {}` and `one sig False extends Bool {}` (declared
  together: `one sig True, False extends Bool {}`)
- `pred isTrue(b: Bool)` · `pred isFalse(b: Bool)`
- `Not(b: Bool): Bool` ⟨one⟩ · `And(b1: Bool, b2: Bool): Bool` ·
  `Or(b1, b2: Bool): Bool` · `Xor(b1, b2: Bool): Bool` ·
  `Nand(b1, b2: Bool): Bool` · `Nor(b1, b2: Bool): Bool`
- `[private] subset_(s1: set Bool, s2: set Bool): Bool`  ⟨**private** helper —
  hidden name⟩

### 7.4 `util/natural` (no params)

- Opens (**both private**): `private open util/ordering[Natural] as ord`;
  `private open util/integer as integer` (so `ord/…` and `integer/…` are *not*
  re-exported through `util/natural`).
- `sig Natural {}`
- `one sig Zero in Natural {}`  ⟨`one`, **subset (`in`)** of Natural⟩
- `lone sig One in Natural {}`  ⟨`lone`, subset of Natural — empty when
  scope < 2⟩
- Anonymous `fact { … }` (constrains `Zero`/`One` to the order's first/second).
- `inc(n: Natural): lone Natural` · `dec(n: Natural): lone Natural`
- `add(n1: Natural, n2: Natural): lone Natural` · `sub(n1, n2: Natural): lone
  Natural` · `mul(n1, n2: Natural): lone Natural` · `div(n1, n2: Natural): lone
  Natural`  ⟨all results `lone`, may be empty⟩
- `pred gt(n1, n2: Natural)` · `pred lt(n1, n2: Natural)` ·
  `pred gte(n1, n2: Natural)` · `pred lte(n1, n2: Natural)`
- `max(ns: set Natural): lone Natural` · `min(ns: set Natural): lone Natural`

### 7.5 `util/sequence[elem]` (sequences reified as `Seq` atoms)

- Opens: `open util/ordering[SeqIdx] as ord`.
- `sig SeqIdx {}`  ⟨no fields⟩
- `sig Seq { seqElems: SeqIdx -> lone elem }`  ⟨**field name is `seqElems`**, type
  `SeqIdx -> lone elem`; sig has an appended fact constraining a prefix⟩
- Public `fact canonicalizeSeqs` (no two `Seq` atoms share a `seqElems`).
- **Predicates**: `pred noDuplicates()` ⟨0-ary⟩ · `pred allExist()` ⟨0-ary⟩ ·
  `pred allExistNoDuplicates()` ⟨0-ary⟩ · `pred rest(s: Seq, r: Seq)` ·
  `pred isEmpty(s: Seq)` · `pred hasDups(s: Seq)` ·
  `pred startsWith(s: Seq, prefix: Seq)` ·
  `pred add(s: Seq, e: elem, added: Seq)` ·
  `pred setAt(s: Seq, idx: SeqIdx, e: elem, setted: Seq)` ·
  `pred insert(s: Seq, idx: SeqIdx, e: elem, inserted: Seq)` ·
  `pred copy(source: Seq, dest: Seq, destStart: SeqIdx)` ·
  `pred append(s1: Seq, s2: Seq, appended: Seq)` ·
  `pred subseq(s: Seq, sub: Seq, from: SeqIdx, to: SeqIdx)`
  ⟨note: here `add/setAt/insert/copy/append/subseq` are **preds** (relate input
  and output seqs), unlike seqrel/sequniv where they are funcs⟩
- **Funcs**: `at(s: Seq, i: SeqIdx): lone elem` · `elems(s: Seq): set elem` ·
  `first(s: Seq): lone elem` · `last(s: Seq): lone elem` ·
  `inds(s: Seq): set SeqIdx` · `lastIdx(s: Seq): lone SeqIdx` ·
  `afterLastIdx(s: Seq): lone SeqIdx` · `idxOf(s: Seq, e: elem): lone SeqIdx` ·
  `lastIdxOf(s: Seq, e: elem): lone SeqIdx` · `indsOf(s: Seq, e: elem): set
  SeqIdx` · `firstIdx(): SeqIdx` ⟨0-ary, effective `one`⟩ · `finalIdx(): SeqIdx`
  ⟨0-ary, `one`⟩.
  Disambiguation: **`first`/`last`** take a `Seq` and return the first/last
  *element* (`lone elem`); **`firstIdx`/`finalIdx`** are 0-ary and return the
  first/last *index* of the whole `SeqIdx` order (`one SeqIdx`); **`lastIdx`**
  takes a `Seq` and returns its last occupied *index* (`lone SeqIdx`);
  **`afterLastIdx`** takes a `Seq` and returns the next free index (`lone
  SeqIdx`).

### 7.6 `util/seqrel[elem]` (sequences as a bare `SeqIdx -> elem` relation)

- Opens: `open util/integer` (no alias → auto-aliased `integer`);
  `open util/ordering[SeqIdx] as ord`.
- `sig SeqIdx {}`  ⟨no `Seq` sig — a sequence is any `SeqIdx -> elem` value⟩
- `pred isSeq(s: SeqIdx -> elem)`
- All operations are **funcs** returning `SeqIdx -> elem` (contrast §7.5):
  `elems(s: SeqIdx -> elem): set elem` · `first(s: SeqIdx -> elem): lone elem` ·
  `last(s: SeqIdx -> elem): lone elem` ·
  `rest(s: SeqIdx -> elem): SeqIdx -> elem` ·
  `butlast(s: SeqIdx -> elem): SeqIdx -> elem` ·
  `pred isEmpty(s: SeqIdx -> elem)` · `pred hasDups(s: SeqIdx -> elem)` ·
  `inds(s: SeqIdx -> elem): set SeqIdx` ·
  `lastIdx(s: SeqIdx -> elem): lone SeqIdx` ·
  `afterLastIdx(s: SeqIdx -> elem): lone SeqIdx` ·
  `idxOf(s: SeqIdx -> elem, e: elem): lone SeqIdx` ·
  `lastIdxOf(s: SeqIdx -> elem, e: elem): lone SeqIdx` ·
  `indsOf(s: SeqIdx -> elem, e: elem): set SeqIdx` ·
  `add(s: SeqIdx -> elem, e: elem): SeqIdx -> elem` ·
  `setAt(s: SeqIdx -> elem, i: SeqIdx, e: elem): SeqIdx -> elem` ·
  `insert(s: SeqIdx -> elem, i: SeqIdx, e: elem): SeqIdx -> elem` ·
  `delete(s: SeqIdx -> elem, i: SeqIdx): SeqIdx -> elem` ·
  `append(s1: SeqIdx -> elem, s2: SeqIdx -> elem): SeqIdx -> elem` ·
  `subseq(s: SeqIdx -> elem, from: SeqIdx, to: SeqIdx): SeqIdx -> elem` ·
  `firstIdx(): SeqIdx` ⟨0-ary, one⟩ · `finalIdx(): SeqIdx` ⟨0-ary, one⟩.
  ⟨seqrel has `butlast` and `delete` (sequence has neither); sequence has
  `copy`/`startsWith`/`noDuplicates`/`allExist*` (seqrel has none)⟩

### 7.7 `util/sequniv` (the `seq` keyword's module; sequences as `Int -> univ`)

Do **not** open manually — the `seq` field keyword auto-opens this aliased `seq`
(§4.5). Sequences are `Int -> univ` relations indexed by `seq/Int`.

- Opens: `open util/integer as ui`. No sigs.
- `pred isSeq(s: Int -> univ)` · `pred isEmpty(s: Int -> univ)` ·
  `pred hasDups(s: Int -> univ)`
- Funcs (note **dependent result types** referring to the param `s`):
  `elems(s: Int -> univ): set (Int.s)` · `first(s: Int -> univ): lone (Int.s)` ·
  `last(s: Int -> univ): lone (Int.s)` · `rest(s: Int -> univ): s` ·
  `butlast(s: Int -> univ): s` · `inds(s: Int -> univ): set Int` ·
  `lastIdx(s: Int -> univ): lone Int` · `afterLastIdx(s: Int -> univ): lone Int` ·
  `idxOf(s: Int -> univ, e: univ): lone Int` ·
  `lastIdxOf(s: Int -> univ, e: univ): lone Int` ·
  `indsOf(s: Int -> univ, e: univ): set Int` ·
  `add(s: Int -> univ, e: univ): s + (seq/Int -> e)` ·
  `setAt(s: Int -> univ, i: Int, e: univ): s + (seq/Int -> e)` ·
  `insert(s: Int -> univ, i: Int, e: univ): s + (seq/Int -> e)` ·
  `delete(s: Int -> univ, i: Int): s` ·
  `append(s1: Int -> univ, s2: Int -> univ): s1 + s2` ·
  `subseq(s: Int -> univ, from: Int, to: Int): s`.

### 7.8 `util/relation` (no params)

**Param shapes are NOT uniform** — arity varies by predicate:

- Funcs (dependent results): `dom(r: univ -> univ): set (r.univ)` ·
  `ran(r: univ -> univ): set (univ.r)`
- Preds taking `(r, s: set univ)`: `total`, `functional`, `function`,
  `surjective`, `injective`, `bijective`, `acyclic`, `preorder`, `equivalence`,
  `partialOrder`, `totalOrder` — each `pred name(r: univ -> univ, s: set univ)`.
  (`reflexive(r: univ -> univ, s: set univ)` too.)
- Preds taking **only `(r)`**: `pred irreflexive(r: univ -> univ)` ·
  `pred symmetric(r: univ -> univ)` · `pred antisymmetric(r: univ -> univ)` ·
  `pred transitive(r: univ -> univ)`
- Pred taking **three** params:
  `pred bijection(r: univ -> univ, d: set univ, c: set univ)`
- Pred whose set param is declared **bare `univ`** (not `set univ`):
  `pred complete(r: univ -> univ, s: univ)`  ⟨the lone exception; every other
  domain param is `set univ`⟩

### 7.9 `util/graph[node]` (no int)

- Opens: `open util/relation as rel`.
- Preds taking only `(r)`: `pred undirected(r: node -> node)` ·
  `pred noSelfLoops(r: node -> node)` · `pred weaklyConnected(r: node -> node)` ·
  `pred stronglyConnected(r: node -> node)` · `pred ring(r: node -> node)` ·
  `pred dag(r: node -> node)` · `pred forest(r: node -> node)` ·
  `pred tree(r: node -> node)`
- Preds taking `(r, root: node)`: `pred rootedAt(r: node -> node, root: node)` ·
  `pred treeRootedAt(r: node -> node, root: node)`
- Funcs: `roots(r: node -> node): set node` · `leaves(r: node -> node): set node`
  · `innerNodes(r: node -> node): set node`

### 7.10 `util/ternary` (no params)

All funcs take `r: univ -> univ -> univ`; result types are dependent projections:

- `dom(r): set ((r.univ).univ)` · `ran(r): set (univ.(univ.r))` ·
  `mid(r): set (univ.(r.univ))`
- `select12(r): r.univ` · `select23(r): univ.r` ·
  `select13(r): ((r.univ).univ) -> (univ.(univ.r))`
- `flip12(r): (univ.(r.univ)) -> ((r.univ).univ) -> (univ.(univ.r))` ·
  `flip13(r): (univ.(univ.r)) -> (univ.(r.univ)) -> ((r.univ).univ)` ·
  `flip23(r): ((r.univ).univ) -> (univ.(univ.r)) -> (univ.(r.univ))`

### 7.11 `util/time` (**header-less** module — no `module` line)

Confirms header-less modules are legal (the module path is inferred from the
open/filename). This module is **mostly macros**, not funcs:

- Opens: `open util/ordering[Time]` (no alias → auto-aliased `ordering`).
- `sig Time {}`
- Macros (`let` paragraphs — expand by substitution, §3.7):
  - `dynamic(x)` ⟨1 param⟩ · `dynamicSet(x)` ⟨1 param⟩
  - `then(a, b, t, t")` ⟨**4 params; the 4th param name is `t"`** — the trailing
    `"` is a legal identifier char (grammar §1.4), *not* a string⟩
  - `while()` ⟨0-param macro, defined as `while = while3`⟩
  - `while0(cond, body, t, t")` … `while9(cond, body, t, t")` ⟨10 macros, each
    4 params `cond, body, t, t"`⟩
  ⟨macro params carry no type annotations — they are textual, §3.7. The `"`-in-
  name quirk also appears as bound vars `s"`, `i"`, `x"` in seqrel/sequniv/
  sequence bodies; mettle's lexer already accepts it (grammar §1.4).⟩

---

## 8. Determinism notes (mettle must be deterministic even where the jar is sloppy)

The reference is *mostly* deterministic here because it uses `LinkedHashMap`/
`SafeList`/`ArrayList` (insertion order) for sigs, opens, params, funcs, facts,
commands, and `new2old`. mettle mirrors **insertion order** for all of these (D2,
R8): resolve sigs in declaration order, fields in `new2old` order, commands in
source order.

Genuinely order-**incidental** spots mettle must pin deliberately (not copy the
JVM's order):

- **Warning order.** `ExprList.implicits` is a `HashMap<Pos,String>` and
  `Context.visit(ExprList)` iterates its `entrySet()` — implicit-conjunction
  warning order is JVM-incidental. mettle emits warnings in a fixed order (e.g.
  by source `Span`).
- **`errors.pick()`** returns the first `JoinableList` error, which follows
  resolution order — deterministic given insertion-order resolution, but mettle
  should *choose* "first by source position" as its contract so the single
  surfaced error is stable and caret-friendly (E3/G3).
- **`resolveModules` merge tiebreak** uses `$`-in-path then `Util.slashComparator`
  — deterministic; reproduce that comparator's total order.
- `sig2module`/`topo` are `HashMap`/`HashSet` used for **membership only**
  (never iterated for output) — safe to back with any map (STYLE D3).

Since mt-020 measures only ACCEPT/REJECT (and, secondarily, the *set* of
warnings, not their order), warning-order incidentalness does not affect the
gauge — but mettle's own output must still be byte-stable (U4).

---

## 9. Open questions / residual uncertainty (be honest)

- **Exact relevance-warning conditions** are intricate (they depend on the
  top-down relevant type at each node). This document pins the *catalog* and the
  accept/reject boundary precisely; the precise firing condition of each
  individual warning should be re-derived per-node from `ExprUnary.resolve`/
  `ExprBinary.resolve` when mt-018 implements warnings, and each disagreement
  filed as a Ledger entry (mt-020 triage). Warnings are **not** the rung gate.
- **Meta-sig (`$`) semantics** are pinned structurally (§1 phase 8) but mettle
  may defer full meta support until a model in the corpus needs it (none in
  alloytools-models rely on `sig$` beyond parse); flag via LIMITATIONS if so.
- **`computeModulePath` corner cases** — resolved by mt-017. The exact reading:
  cancel the **common leading prefix** of (parent's declared module name, target)
  first, then climb by the *remaining* module depth + 1 and re-root only the
  remaining target. jar-verified 2026-07-16 on real mislocated modules
  (portus-63 zigbee: `module zigbee_join/base/event` at `trunk/base/event.als`
  opening `zigbee_join/base/types` → ACCEPT, so the open must resolve to
  `trunk/base/types.als`); unit fixtures live in `als-types/src/path.rs`.
- The GUI's fatal-warning preference (§5.3) is out of scope but worth a one-line
  LIMITATIONS note so nobody wires it into `mettle check`.

---

## 10. Probe log (jar-verified 2026-07-15)

Harness: `scratchpad/probe/ProbeShim.java` — calls
`CompUtil.parseEverything_fromString(rep, code)` (the mt-020 entry point) with a
warning-capturing `A4Reporter`; reports ACCEPT / REJECT (+ throwing class#method)
/ warnings. Oracle: `oracle/org.alloytools.alloy.dist.jar` (6.2.0), OpenJDK 21.
All verdicts below are the jar's observed behavior; where source and jar could
differ, **the jar wins** (none diverged).

| # | Case | Verdict |
|---|---|---|
| 01 | `no (A & none)` fact | ACCEPT + `&`-irrelevant warning (warnings non-fatal) |
| 02 | `a.n = 1` (Int field vs int literal) | ACCEPT (both `is_int`) |
| 03 | `#(1+2) = 2` | ACCEPT (`+` is union: `{1,2}`) |
| 04 | `plus[1,2] = 3` via `util/integer` | ACCEPT |
| 05 | duplicate `sig A` | REJECT `dup` |
| 06 | overlapping sigs, same field `f` | REJECT `rejectNameClash` |
| 07 | `A extends B`, `B extends A` | REJECT `resolveSig` (cyclic) |
| 08 | unknown name in fact | REJECT `hint` |
| 09 | `Color/first` on an enum | REJECT `hint` (no `EnumName/` namespace) |
| 10 | `s: seq A` field | ACCEPT (opens `util/sequniv`) |
| 11 | `module Wrong` (≠ filename) | ACCEPT (root name unchecked) |
| 12 | recursive `pred p[a]{p[a]}` | ACCEPT (no recursion check) |
| 13 | `A = f` (arity 1 vs 2) | REJECT `ExprBinary.error` |
| 14 | `some f` at top level | ACCEPT (bare field = whole relation) |
| 15 | two `fun foo` genuinely ambiguous | REJECT `ExprChoice.resolveHelper` |
| 20 | enum `first`, `Red.next` unqualified | ACCEPT |
| 21 | enum `ordering/first` | ACCEPT (auto-alias `ordering`) |
| 22/23 | sig fact using own field (implicit `this`) | ACCEPT |
| 24 | two identical `open util/ordering[A]` | ACCEPT (deduped) |
| 25 | `open …[A] as oa`, `…[B] as ob` | ACCEPT (distinct instances) |
| 26 | two modules, same alias `x` | REJECT `addOpen` |
| 27 | `private sig A` (single file) | ACCEPT |
| 28 | `name: String`, `= "hello"` | ACCEPT |
| 29 | `sig C in A + B` (multi-parent subset) | ACCEPT |
| 30 | `abstract sig A` no children | ACCEPT |
| 31 | `open util/ordering` (missing arg) | REJECT `resolveParams` |
| 32/33 | `run`/`check` of missing target | REJECT `resolveCommand` |
| 34 | scope on missing sig | REJECT `resolveCommand` |
| 35 | `fun g: A { f }` (body arity 2) | REJECT `Func.setBody` |
| 40 | unused quantifier var | ACCEPT + "variable is unused" warning |
| 43 | top-level `let` macro | ACCEPT |
| 44 | `some sig$` (meta) | ACCEPT (triggers `resolveMeta`) |
| 60/61 | only-a-sig / comment-only (empty) | ACCEPT (no ghost sig) |
| 62 | `module` not first | REJECT `addModelName` (SYNTAX, mt-013) |
| 63 | `sig A$B` (`$` in name) | REJECT `CUP…nod` (SYNTAX, mt-013) |
| 64 | `open util/ordering[none]` | REJECT `resolveParams` |
| 67 | two facts named `F` | ACCEPT (facts don't check names) |
| 68 | two `pred p {}` | ACCEPT (funcs/preds overload) |

Anything this document leaves ambiguous: **test against the jar first** (extend
`ProbeShim`), record the answer here (accept/reject) or in SEMANTICS_LEDGER.md
(behavior), then implement.
