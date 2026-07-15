# PORTING_RULES.md — Java (Alloy/Kodkod) -> idiomatic Rust

Purpose: the enforced translation rubric for reimplementing Alloy 6 / Kodkod behavior in Rust. Cite these rules by number in review.

Status: living document (see "Proposing changes" at the end).

Prime directive: **pin the behavior, not the structure.** Read the Java until you can state the behavior in one sentence, record it in the Semantics Ledger with a test (STYLE §12), then write the Rust the way Rust wants it. Porting Java shape verbatim is both a quality smell and a legal risk (see Legal hygiene).

---

## 1. Visitor pattern / `instanceof` dispatch -> enum + `match`

Closed set of node kinds becomes one enum; dispatch is exhaustive `match`. No visitor interface, no double-dispatch.

```java
// Java
abstract class Expr { abstract <T> T accept(Visitor<T> v); }
if (e instanceof Binary b) { ... }
```
```rust
// Rust
enum Expr { Binary(Binary), Unary(Unary), Var(VarId), /* ... */ }
match expr {
    Expr::Binary(b) => /* ... */,
    Expr::Unary(u)  => /* ... */,
    // exhaustive: a new variant forces every site to update
}
```
Rule R1: exhaustive match, no catch-all `_` on core AST/IR enums (so new variants surface every unhandled site).

## 2. Class hierarchy / inheritance -> closed enum OR open trait

- R2a. Fixed, known-at-compile-time kinds (AST/IR node families, operators) -> **closed enum**. Prefer this; it gives exhaustiveness and no dynamic dispatch.
- R2b. Genuinely open extension points where callers plug in implementations (e.g. the `Solver` backend) -> **trait**. Use `dyn` only at that boundary.

```java
// Java: abstract Solver with subclasses
abstract class Solver { abstract Solution solve(Formula f); }
```
```rust
// Rust: trait only for the open boundary
trait Solver { fn solve(&mut self, f: &Cnf) -> Solution; }
// AST operators stay a closed enum, not a trait object
enum BinOp { Join, Union, Intersect, /* ... */ }
```
Rule R2: default to enum; reach for a trait only when the extension set is truly open. Don't model a fixed AST as trait objects.

## 3. Mutable object graphs / bidirectional refs -> arena + typed IDs

No `Rc<RefCell<...>>`, no parent pointers by reference. `Vec<T>` arena + newtype index IDs (STYLE §6).

```java
// Java
class Node { Node parent; List<Node> children; }
```
```rust
// Rust
struct NodeId(u32);
struct Node { parent: Option<NodeId>, children: Vec<NodeId> }
struct Ast { nodes: Vec<Node> } // owns the arena; IDs index into it
```
Rule R3: cross-references are IDs resolved through the owning arena. Never `Rc<RefCell>` to emulate Java aliasing.

## 4. Exceptions -> `Result` / typed errors

- R4a. Checked exceptions -> variants of a `thiserror` error enum; the `throws` set becomes the enum's variants.
- R4b. Unchecked exceptions that signal genuine internal invariant violations -> `panic!`/`unreachable!` (STYLE §E2) — but only if truly unreachable by construction; anything reachable from user input is a `Result`.

```java
// Java
Sig resolve(String n) throws SyntaxError { if (bad) throw new SyntaxError(n); }
```
```rust
// Rust
#[derive(thiserror::Error, Debug)]
enum ResolveError { #[error("unknown name `{0}` at {1:?}")] Unknown(String, Span) }
fn resolve(n: &str) -> Result<SigId, ResolveError> { /* ... */ }
```
Rule R4: no exception-for-control-flow. Errors are values, carry a span, stay typed until the CLI (STYLE §E3).

## 5. `null` -> `Option`; sentinels -> `Option`/enum

```java
// Java
Sig parent = sig.parent;      // may be null
int idx = list.indexOf(x);    // -1 sentinel
```
```rust
// Rust
let parent: Option<SigId> = sig.parent;
let idx: Option<usize> = list.iter().position(|e| e == &x);
```
Rule R5: no in-band sentinels (`-1`, `""`, `Integer.MIN_VALUE`, magic node). Absence is `Option`; a small closed set of states is an enum. Never a "null object".

## 6. Overloaded methods / optional args -> distinct fns or builder

Java overloading and default-arg patterns become explicitly named functions or a builder. Be explicit; no boolean-blindness.

```java
// Java
Bounds bound(Sig s);
Bounds bound(Sig s, int scope);
Bounds bound(Sig s, int scope, boolean exact);
```
```rust
// Rust: name the intent
fn bound_default(s: SigId) -> Bounds;
fn bound_scoped(s: SigId, scope: u32) -> Bounds;
fn bound_exact(s: SigId, scope: u32) -> Bounds;
// or a builder when args grow:
Bounds::builder(s).scope(3).exact(true).build();
```
Rule R6: prefer distinctly named functions; use a builder when the option set is large. No `Option<bool>` "maybe-default" params carrying three meanings.

## 7. Static mutable / singletons -> explicit context

No `static mut`, no global registries, no thread-local singletons. Pass a context/arena reference explicitly. This is also a determinism requirement (STYLE §1).

```java
// Java
class Factory { static Factory INSTANCE = new Factory(); int next; }
```
```rust
// Rust
struct Ctx { next_var: u32, sigs: Vec<Sig> }
fn translate(ctx: &mut Ctx, /* ... */) { /* threads ctx explicitly */ }
```
Rule R7: all mutable state is owned and passed; zero global mutable state. Counters (e.g. variable numbering) live in an explicit context so numbering is reproducible.

## 8. Java iteration-order pitfalls -> deterministic collections

`HashMap`/`HashSet` iteration order in Java is unspecified and JVM-dependent; do not port order-dependent loops naively, and do not reproduce the JVM's order.

```java
// Java — order is incidental, often relied on by accident
for (Map.Entry<String,Sig> e : sigMap.entrySet()) { number(e); }
```
```rust
// Rust — pick and document the order you actually want
use indexmap::IndexMap;
let sigs: IndexMap<String, Sig> = /* insertion order */;
for (name, sig) in &sigs { number(sig); }
// or BTreeMap for name-sorted, or collect+sort_by_key
```
Rule R8: any loop that influences numbering/CNF/output uses `IndexMap`/`BTreeMap`/sorted `Vec` with the intended order stated (STYLE §7). When mirroring Java, decide the order deliberately — self-consistent, not jar-matching.

## 9. Other recurring Java idioms

- R9a. `Iterator`/`Iterable` + `while (it.hasNext())` -> Rust `Iterator` adapters (`map`/`filter`/`fold`); avoid manual index loops unless indexing IDs.
- R9b. `Comparable`/`compareTo` -> `Ord`/`PartialOrd` derives or explicit `sort_by_key`; keep ordering total and deterministic.
- R9c. `equals`/`hashCode` -> `PartialEq`/`Eq`/`Hash` derives; ensure keys used in deterministic maps have stable, value-based hashing.
- R9d. `StringBuilder` accumulation -> `String` + `write!`/`fmt::Display`; pretty-printer implements `Display`, snapshot-tested (STYLE §U2).
- R9e. Java `int`/`long` wraparound semantics -> match Alloy's observed integer/bitwidth behavior exactly; pick `i32`/`i64`/wrapping ops per the Semantics Ledger entry, never "whatever Rust defaults to".

---

## Legal hygiene

- Reimplementing **behavior** and **APIs** from reading the Java is fine — behavior and interfaces are not copyrightable. That is the whole method (STYLE §12): read, state the behavior in one sentence, test, reimplement idiomatically.
- The risk is porting **verbatim structure** — copying class layouts, method decomposition, or line-by-line logic. Idiomatic reimplementation (enums, arenas, `Result`) is precisely what keeps mettle's non-derivative posture clean. If a Rust file mirrors a Java file class-for-class, that's a red flag in review.
- Attribution obligations to keep in mind (updated per [ADR-0006](docs/adr/0006-licensing-posture.md)):
  - Reference analyzer (Alloy): upstream's license is **unsettled** (MIT/Apache-2.0 transition in progress; see the reference brief §2) — behavior may be studied and reimplemented; never copy source text, and never assume a settled upstream license.
  - Kodkod is MIT — same posture; reimplement, don't copy.
  - Standard-library models (`util/*.als`) are a **clean-room rewrite** (ADR-0006): implement from the documented module interfaces + Ledger-pinned behavior. Never copy from — or write with open — upstream's `util/*.als` text; the copies under `corpus/alloytools-models/models/util/` are conformance test *inputs*, off-limits as source material.
  - mettle's own code is MPL-2.0 (root `LICENSE`); corpora are local-only and never redistributed.
- When unsure whether something is behavior (OK to reimplement) or expression (do not copy), treat it as expression and reimplement from a one-sentence behavioral spec.

---

## Proposing changes

This rubric is enforced, not advisory. Agents follow it; they do not reshape it unilaterally. To change a rule: open a brief human-approved note (ADR under `docs/adr/`) stating the rule touched, the rationale, and the impact. Reference the ADR in the PR that edits this file. Until an ADR lands, the current text governs review.
