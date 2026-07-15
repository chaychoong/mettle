# Alloy 6 surface syntax — pinned contract for mettle's lexer & parser

This document pins **exactly what the reference implementation accepts**, derived
from the pinned oracle build (ADR-0002, commit `794226dd` — the jar's own
`Git-SHA`) by reading its grammar sources and verifying the load-bearing facts
against the jar itself. It is the **fixed contract** for mt-010 (lexer) and
mt-011 (parser): implement *this*, not the (incomplete) public grammar appendix
and not memory.

Provenance (all at commit `794226dd07b536fe35c5ca44b529417183cd629b`):
- `org.alloytools.alloy.core/parser/Alloy.lex` — token definitions (JFlex).
- `org.alloytools.alloy.core/parser/Alloy.cup` — grammar + parse-time checks (CUP).
- `.../edu/mit/csail/sdg/parser/CompFilter.java` — token-stream rewrites between lexer and parser.
- `.../edu/mit/csail/sdg/alloy4/Version.java` — `experimental = true` is **compiled in**
  (verified empirically 2026-07-15: the jar accepts string literals and `1..4 steps`
  range scopes, and rejects `'` in identifiers).

Per PORTING_RULES (legal hygiene): these files were **read to pin behavior**;
mettle's implementation is written fresh against this document, never by
transcribing their text or structure.

---

## 1. Lexical rules

Input is UTF-8 text. Whitespace: space, `\t`, `\f`, `\r`, `\n` — skipped.

### 1.1 Comments
- Line: `//` or `--` to end of line.
- Block: `/* ... */` and `/** ... */`, **non-nesting**, terminated by the first `*/`.
  (An unterminated block comment runs to EOF without error in JFlex `~` semantics —
  mettle should instead report a precise "unterminated comment" error; divergence
  is impossible on well-formed input. Note in LIMITATIONS if ever observed.)

### 1.2 Operator / punctuation tokens
Longest match wins:

| Token | Spellings | Token | Spellings |
|---|---|---|---|
| `Not` | `!` | `Arrow` | `->` |
| `Hash` | `#` | `Minus` | `-` |
| `And` | `&&` | `Dot` | `.` and `::` |
| `Ampersand` | `&` | `Slash` | `/` |
| `LParen RParen` | `(` `)` | `RangeRestrict` | `:>` |
| `Star` | `*` | `Colon` | `:` |
| `PlusPlus` | `++` | `Iff` | `<=>` |
| `Plus` | `+` | `Lte` | `<=` and `=<` |
| `Comma` | `,` | `DomRestrict` | `<:` |
| `Shl` | `<<` | `Lt` | `<` |
| `Implies` | `=>` | `Equals` | `=` |
| `Shr` | `>>>` | `Sha` | `>>` |
| `Gte` | `>=` | `Gt` | `>` |
| `At` | `@` | `LBracket RBracket` | `[` `]` |
| `Caret` | `^` | `LBrace RBrace` | `{` `}` |
| `Or` | `\|\|` | `Bar` | `\|` |
| `Tilde` | `~` | `Semi` | `;` |
| `Prime` | `'` and U+2018 `‘` and U+2019 `’` | | |

Notes: `::` is an exact synonym for `.`. There is **no** `==` token (only `=`).
The three prime spellings are identical tokens.

### 1.3 Keywords
Reserved words (each its own token; never identifiers):

```
abstract all and as assert but check disj else enum exactly expect extends
fact for fun iden iff implies in int Int let lone module none no not one
open or pred private run seq set sig some steps String sum this univ var
always after before eventually historically once releases since triggered until
```

Case-sensitive. `Int` (sig-ref) and `int` (cast) are **distinct tokens**; likewise
`String` is a keyword but `string` is an identifier. `steps` is a keyword.
`or`=`||`, `and`=`&&`, `iff`=`<=>`, `implies`=`=>`, `not`=`!` are alternate
spellings of the same tokens.

### 1.4 Identifiers
`start-char (continue-char)*` where, in the reference, *start* is Java's
`isJavaIdentifierStart` (Unicode letters, `_`, `$`, currency symbols) and
*continue* is `isJavaIdentifierPart` **plus the double-quote character `"`**
(a legacy quirk: `a"b` is one identifier).

- `'` is **not** an identifier character (Alloy 6 change: it is the prime
  operator). Verified: `sig B'' {}` is a syntax error in the jar.
- `$` may appear in identifiers at the lexer level, but every *declaration*
  site rejects names containing `$` ("The name cannot contain the '$' symbol.").
- mettle rule: ASCII exactly as above (`[A-Za-z_$]` then `[A-Za-z0-9_$"]`);
  for non-ASCII use `char::is_alphabetic` (start) / `is_alphanumeric`
  (continue). This can diverge from Java's classes only for exotic Unicode —
  record in LIMITATIONS, gauge via corpus.

### 1.5 Number literals
All are non-negative `i32` (`Integer.parseInt` range); out-of-range is a
lex-time error.

The reference's JFlex longest-match + first-rule tie-breaking makes the
raw patterns misleading; the **behavioral** rule (jar-verified 2026-07-15,
all six cases below) is: starting at a digit, take the **maximal run of
name-follow characters** — the ASCII class `[$0-9a-zA-Z_"]` exactly (a
non-ASCII letter after a digit starts a fresh token instead) — then
classify the whole run:

- all decimal digits ⇒ decimal literal (**no underscores**: `1_000` is
  REJECTED by the jar — the name-error rule wins the tie);
- `0x` + a sequence of `_`s and **pairs of hex digits** consuming the entire
  rest of the run ⇒ hex literal, underscores stripped (`0x12`, `0x_12`,
  `0x_ff_01` OK; `0x1`, `0x123`, `0x1_2` REJECTED);
- `0b` + `[01_]+` consuming the entire rest of the run ⇒ binary literal,
  underscores stripped (`0b1_0` OK; `0b12` REJECTED);
- anything else ⇒ the error "Name cannot start with a number." spanning the
  whole run (so `3x`, `1_000`, `0x123`, `0b12` are all this error).

Negative literals do not exist in the lexer; see filter rule F3.

### 1.6 String literals
Supported (experimental is on in the pinned jar). `"..."` on one line;
escapes exactly `\\`, `\n`, `\"`; empty string `""` is an error ("Empty
string is not allowed…"); unterminated strings are errors. A closing quote
immediately followed by any name-follow character (the same ASCII class as
§1.5, **including digits and `"`**) is the error "String literal cannot be
followed by a legal identifier character" — jar-verified: `"ab"9` and
`"a""b"` are both rejected. Value stored unescaped.

---

## 2. Token-stream rewrites (the reference's CompFilter)

The reference parser does not consume raw tokens; a filter rewrites the
stream. mettle may implement these as lexer post-pass or parser lookahead,
but the **observable behavior must match**. In pipeline order:

- **F1 — command label reorder.** `ID : (run|check) X` where `X` is an
  identifier or `{` ⇒ treat `ID` as the command's label: `label: run p` ≡
  the labeled command. (Reference literally reorders tokens to `run ID X`.)
- **F2 — merges** (whitespace/comments allowed between parts):
  - `not`/`!` + one of `in = < > <= >= =<` ⇒ a single negated-comparison token.
  - `pred` `/` `totalOrder` ⇒ builtin name `pred/totalOrder`.
  - `fun` `/` one of `add sub mul div rem` ⇒ the integer **binary operator**
    `fun/add` …; `fun` `/` one of `min max next` ⇒ the builtin **constant**
    `fun/min` `fun/max` `fun/next`.
  - Arrow multiplicities: `m -> n` where `m,n ∈ {some, one, lone, set}` and
    either side optional ⇒ one arrow token carrying both multiplicities
    (`set` ≡ unannotated side; 16 combinations total).
- **F3 — unary minus.** `-` immediately followed by a number literal folds
  into a negative literal **unless** the previous token can end an expression:
  `) ] } disj int sum iden this univ Int none` , `pred/totalOrder`,
  `fun/min|max|next`, an identifier, a number, or a string.
  (So `x = -1` is a literal; `n - 1` is set difference / nothing folds.)
- **F4 — quantifier disambiguation.** `all no some lone one sum` become
  *quantifiers* (rather than unary tests / multiplicities) iff the previous
  token is not `:` or `disj`, and lookahead matches
  `[private] [disj] ID (, ID)* :`. Otherwise they stay unary/multiplicity.
  (`some x: A | p` = quantifier; `some x` = nonemptiness test; in `y: one A`
  the `one` follows `:` so it is always a multiplicity.)

---

## 3. Operator precedence (weakest → tightest)

Derived from the production stratification in `Alloy.cup` (the CUP
`precedence` block only resolves its ambiguities; the levels live in the
productions).

| # | Operators | Assoc / shape |
|---|---|---|
| 1 | `;` (formula sequencing) | right; `a ; b` ≡ `a && after b` — keep as a `Seq` node in the AST |
| 2 | `let`, quantifiers `all no some lone one sum` + decls + `\|`/block | body extends maximally right; a binder may appear as a **rightmost operand, subject to the one-hop budget rule** (see §3.1) |
| 3 | `\|\|` `or` | left |
| 4 | `<=>` `iff` | left |
| 5 | `=>` `implies` (optional `else`) | right; `else` binds to the nearest unmatched `implies` (dangling-else) |
| 6 | `&&` `and` | left |
| 7 | `until releases since triggered` | left |
| 8 | prefix `! not always eventually after before historically once` | prefix; **looser than comparisons**: `!a = b` ≡ `!(a = b)` (when not merged by F2) |
| 9 | comparisons `= in < > <= >= =<` and negated forms; prefix tests `no some lone one set seq` | comparisons left-assoc and chainable (`a=b=c` ≡ `(a=b)=c`); prefix tests apply to a level-10 operand, so `no a = b` ≡ `(no a) = b` |
| 10 | `<< >> >>>` | left |
| 11 | `+ -` `fun/add` `fun/sub` | left |
| 12 | `fun/mul` `fun/div` `fun/rem` | left |
| 13 | prefix `#` `sum` `int` (`sum e`/`int e` = int-cast of `e`) | prefix |
| 14 | `++` | left |
| 15 | `&` | left |
| 16 | `->` with optional multiplicities (16 forms) | **right**: `A->B->C` ≡ `A->(B->C)` |
| 17 | `<:` | left |
| 18 | `:>` | left |
| 19 | `[...]` box join and `.` dot join | postfix, left, same tier interleaving: `a.b[c]` ≡ `(a.b)[c]`, `a[c].b` ≡ `(a[c]).b`; dot's right operand is a level-20 term (`a.~r`, `a.b'` = `a.(b')`) |
| 20 | `'` postfix prime; prefix `~ ^ *` | prefix binds over an inner postfix: `~a'` ≡ `(~a)'` (CUP resolves the shift/reduce toward reduce) |
| 21 | atoms (§4.6) | |

### 3.0 Loose prefixes are NOT valid in tight operands
A prefix operator may only start an operand where its own tier is
grammatically reachable: `a & !b`, `a + no b`, `no !a`, `# no a`,
`a -> !b` are all syntax errors in the jar (jar-verified for the first
two), while `a => !b`, `!!a`, `! no a` are fine. In Pratt terms: gate each
prefix on the current minimum binding power. Binders are the one
exception — see §3.1.

### 3.1 Binder-as-rightmost-operand
The *right* operand of a binary operator may be a full binder (`let`/
quantifier), which then consumes everything to the end of the enclosing
expression: `a + sum x: A \| f[x]` parses with the `sum … \| …` as the whole
right operand of `+`. Postfix `'` may likewise attach to a binder
(`… .(let x = e \| b)'` shape is grammatical).

**This does NOT compose freely across nested precedence levels** (mt-014
correction — the original statement "at every binary level" was too
permissive; ~220 jar probes, table in
[fuzzing.md](fuzzing.md) §2). The jar-verified rule, implemented as
`crate::prec::child_binder_budget` (shared by parser and printer):
- From a fresh expression start, a binder may be the rightmost operand of
  exactly **one** enclosing-operator "hop"; same-tier chains
  (`q and r and all …`) count as one hop (left-assoc nests leftward).
- A second hop (`q or r and all …`) is a syntax error — unless the
  enclosing operator is a bare `implies`/`=>` (no `else`) or the **else**
  branch of `implies … else`, each of which grants its branch a fresh
  budget. The **then** branch of `implies … else` never accepts a bare
  binder.
- Comparisons (`= in < > =< >=`, negated or not) and the set-test prefixes
  (`no some lone one set seq`) never accept a bare binder operand.
- Other prefixes (`!`, temporal unaries, `# sum int`, `~ ^ *`) are
  transparent: they pass the ambient budget through unchanged.
- Parentheses, block/brace bodies, box-join arguments, and decl bounds all
  re-enter as fresh expression starts.

### 3.2 Special dot/bracket targets
- `disj[a,b,…]`, `pred/totalOrder[a,b,…]`, `int[e,…]`, `sum[e,…]` are box
  joins whose target is a builtin name; `a.disj`, `a.pred/totalOrder`,
  `a.int`, `a.sum` are the dot forms. Represent target as a synthesized
  `Name` with that exact text; semantics resolved later.
- `f[]` (empty argument list) is grammatical and means just `f`.

---

## 4. Grammar (shapes, in AST terms)

### 4.1 Module header and opens
- `module qualname [params]` — params are qualified names, each optionally
  `exactly`-marked. At most one header, and it must come before other
  paragraphs (the reference accepts headers anywhere grammatically, then
  errors in `addModelName`; mettle: precise error).
- `[private] open qualname [ sigrefs ] [as name]` — the `[...]` argument
  list may be present-but-empty. A *sigref* is a qualified name or one of
  the keywords `univ`, `Int`, `String`, `steps`, `none`, `seq/Int`
  (represent keyword sigrefs as `Name` with that text).
- Qualified names: `ID (/ ID)*`, plus the special first segments `this/`
  and `seq/`. Whitespace/comments are allowed around `/` (it is a normal
  token). `nod()` rule: declared names must not contain `$`.

### 4.2 Sigs and enums
- `[quals] sig A, B, C [extends P | in P + Q + … | = P + Q + …] { decls } [block]`
  - quals: any order, each at most once: `abstract`, `var`, `private`, one of
    `lone one some`.
  - **`= sigrefs`** (exact subset sig) is grammatical alongside `in` —
    AST: `SigParent::Eq`.
  - Field decls: see §4.4; trailing block = appended fact.
- `enum Name { A, B, C }` — `enum Name {}` is REJECTED by the jar
  (jar-verified); mettle rejects it at parse with a precise error.

### 4.3 Facts, asserts, preds, funs, macros
- `fact [name|string] block`, `assert [name|string] block` — the name can be
  a **string literal** (AST: `ParaName::{Ident,Str}`).
- `[private] pred [SigRef .] name [( decls )|[ decls ]] block`
- `[private] fun  [SigRef .] name [( decls )|[ decls ]] : result block`
  — result is a full expr (multiplicity conversion per §4.4 applies). The
  receiver is a *sigref*, so builtin-sig receivers are legal (jar-verified:
  `fun String.cat[...]` parses).
- Top-level macros: `[private] let name [( names )|[ names ]] (= expr | block)`
  — params are plain names, no bounds. (AST: `Para::Macro`.)

### 4.4 Declarations (fields, params, quantifier/comprehension bindings)
```
[var] [private] [disj] name,+ : [disj] bound-expr
name,+ = expr                     -- "defined" decl (fields); AST: bound wrapped in ExactlyOf
```
- The **left** `disj` states the named relations are mutually disjoint; the
  **right** `disj` (after `:`) is a separate flag (AST: `is_bound_disj`).
- `disj` + `=` is the parse error "Defined fields cannot be disjoint."
- Multiplicity conversion (the reference's `mult()`): when the bound
  expression's top node is unary `some`/`lone`/`one`, it becomes the
  bound-marker form (`SomeOf`/`LoneOf`/`OneOf`). `set e` and `seq e` already
  parse to `SetOf`/`SeqOf` at level 9. Applies to decl bounds and fun results.
- Comprehension decls exclude `=` decls; quantifier decls grammatically allow
  them (jar errors later; mettle: parse then precise error is acceptable —
  Ledger it if ever observed in the wild).
- Trailing comma after decls is tolerated in paragraph decl lists
  (`Decls ::= … | COMMA Decls` — i.e. a *leading* comma is also skipped);
  match the reference: empty decl slots are skipped without error.

### 4.5 Commands and scopes
```
[label :] (run|check) ( qualname | block ) [scope] [expect (0|1)]
```
- Label reordering per F1. Additionally, a command may be **chained**:
  `cmd => run …` / `cmd implies check …` marks the second command as a
  follow-up of the first (AST: `is_followup`; rare, undocumented, but
  grammatical — parse it).
- Scope: `for N [but ts,+]` or `for ts,+` where each *ts* is
  `[exactly] bound target`:
  - bound: `N`, `N..M`, `N..`, each optionally `: I` (increment). All forms
    are accepted by the pinned jar (experimental on). AST: `TypeScope`
    carries `start`, `end: {Same|Bounded(M)|Unbounded}`, `increment`.
  - target: sig qualname, `int`, `Int` (both = bitwidth), `seq`, `String`,
    `steps`; `univ` and `none` are the parse errors "You cannot set a scope
    on univ."/"…none.".
  - Parse-time checks (reference does these in grammar actions — mettle
    reproduces at parse): growing scope on `int`/`Int`/`seq` is an error;
    `exactly` on `int`/`Int`/`seq` is the "exactly keyword is redundant"
    error. `N..N` marks the scope exact even without `exactly`.
- `expect N` — the jar accepts ANY int; only 0 and 1 ever trigger an
  expectation check (other values are carried and ignored). AST:
  `Expect::{Sat,Unsat,Other(i32)}`.
- Scope bound forms, jar-verified: `1:2 A` and `1..5:2 A` accepted;
  `N:I` alone means "from N, unbounded, increment I". `1:2 steps` is
  REJECTED by the jar (steps increments must be 1) — that check lives at
  command-build, mettle defers it to resolve (see LIMITATIONS).

### 4.6 Expression atoms
number (incl. F3-folded negatives) · string · `iden` · `this` · `univ` ·
`none` · `Int` · `String` · `steps` · `seq/Int` · `fun/min` · `fun/max` ·
`fun/next` · `@name` · qualified name · `( expr )` · `{ block }` ·
`{ decls [| body] }` (comprehension; omitted body = `| true`) ·
binders (§3.1).

`{ block }` is any number of formulas conjoined; inside a block, `;`
sequencing composes per level 1. An empty block `{}` is `true`.

---

## 5. Verified pin-points (jar-checked 2026-07-15)

| Fact | Check |
|---|---|
| `fact "named by string" {…}` parses | `commands` on exp1.als exits 0 |
| `for 3 but 1..4 steps` parses | same |
| `sig B'' {}` rejected | CompParser syntax error |
| symmetry/overflow/enumeration facts | see [alloy6-reference.md](alloy6-reference.md) |

Anything this document leaves ambiguous: **test against the jar first**, then
record the answer here (syntax) or in SEMANTICS_LEDGER.md (behavior) before
implementing.
