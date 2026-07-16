# mt-020 — Alloy4Fun differential resolve/typecheck pass (Rung 2 exit gauge)

Evidence doc for bead **mt-020**: a large differential test of mettle's
**name-resolution + type-checker** (`als-types`: `ModuleGraph::load` +
`als_types::resolve`) against the pinned reference jar's post-`resolveAll`
verdict, over the alloy4fun corpus and the 167-file curated corpus. This is the
Rung-2 exit gauge and the [ADR-0009](../adr/0009-fused-resolve-pass-accept-lean.md)
tightening decider. Kept tight and factual, mirroring the mt-013 parse-pass doc
([alloy4fun-error-pass.md](alloy4fun-error-pass.md)).

The gauge is **binary ACCEPT/REJECT** (resolution-doc §0): ACCEPT = `resolveAll`
returns, REJECT = it throws; warnings never count. The one thing that must never
happen is a **jar-accepts / mettle-rejects** disagreement (a drop-in violation).

## 1. Harness

Two sides, both deterministic; all logic lives in
`crates/als-conform/src/bin/resolve_gauge.rs` (the `resolve-gauge` bin) and the
jar shim `crates/als-conform/shim/ResolveGaugeShim.java`.

**mettle side** (`resolve-gauge alloy4fun` / `resolve-gauge paths`): for each
input, run `ModuleGraph::load_with_source` + `als_types::resolve` in-process and
emit `{file, ok, phase, variant}` JSON-Lines. `phase` ∈ {accept, parse, load,
resolve}; `variant` is the `ResolveError` variant. Every run is wrapped in
`catch_unwind` and bucketed as `panic` if it unwinds (**0 panics** over all
150,891 codes). alloy4fun codes load through an empty `MapLoader` (the embedded
clean-room stdlib supplies `util/*` via the normal search order); corpus files
load through `FilesystemLoader` at their real path so multi-file `open`s
resolve. Codes are parallelized across std threads and merged in index order.

**jar side** (`ResolveGaugeShim`): one JVM over a file list, calling
`CompUtil.parseEverything_fromFile(NOP, null, path)` — the real-path 3-arg
`resolveAll` entry (resolution-doc §0). This differs from mt-013's
`ParseOnlyShim`, which calls `parseEverything_fromString` (it writes the code to
a **temp** file, so a relative `open ../sibling` resolves from `/tmp` and
spuriously fails). For self-contained single-file models the two entries are
**verdict-equivalent** (verified: **0/3000** verdict differences on a subset);
for the 167-file corpus (real sibling opens) only `fromFile` is correct — using
`fromString` there produced 14 spurious "File cannot be found" rejects and 1
spurious self-ambiguity, all artifacts of the temp-dir root.

**Reproduce** (jar at `oracle/org.alloytools.alloy.dist.jar`):

```
# mettle side (alloy4fun) — writes codes/, filelist.txt, mettle.jsonl
cargo run --release -p als-conform --bin resolve-gauge -- \
  alloy4fun --corpus corpus/alloy4fun/2024-25 --out <OUT>
# jar side
javac -cp <JAR> -d <CLS> crates/als-conform/shim/ResolveGaugeShim.java
java  -cp <CLS>:<JAR> ResolveGaugeShim <OUT>/filelist.txt > <OUT>/jar.jsonl
# differential
cargo run --release -p als-conform --bin resolve-gauge -- \
  diff --mettle <OUT>/mettle.jsonl --jar <OUT>/jar.jsonl
# corpus (167 files, real paths)
find corpus/alloytools-models/models corpus/portus-63 -name '*.als' | sort > <C>/all.txt
cargo run --release -p als-conform --bin resolve-gauge -- paths <C>/all.txt --out <C>
java -cp <CLS>:<JAR> ResolveGaugeShim <C>/filelist.txt > <C>/jar.jsonl
cargo run --release -p als-conform --bin resolve-gauge -- diff --mettle <C>/mettle.jsonl --jar <C>/jar.jsonl
```

## 2. Dataset & method

`corpus/alloy4fun/2024-25/*.json` — 21 JSON-Lines files, **186,318** records;
the `code` field byte-deduplicated to **150,891** unique texts (matches mt-013).
Dedup is exact (the code text is the map key — no hashing), and the unique set is
sorted lexicographically by bytes, so index N→`codes/NNNNNN.als` is fully
reproducible and `--limit N` yields an honest deterministic prefix. Jar version:
pinned **Alloy 6.2.0**, `Version.experimental = true`.

Budget: mettle side **~34 s** (16 threads, native); jar side **~6–7 min** (one
JVM, `resolveAll` per file). The full set ran; no subsetting was needed.

## 3. Final numbers

### 3.1 Corpus (167 files, real paths) — the drop-in gate

| | count |
|---|---:|
| compared | 167 |
| agree ACCEPT | **167** |
| jar-accepts / mettle-rejects | **0** |
| jar-rejects / mettle-accepts | **0** |

**167/167 = 100% agreement.** (All ACCEPT, matching the mt-013/oracle baselines.)

### 3.2 Alloy4Fun (150,891 unique codes)

| | count | % |
|---|---:|---:|
| compared | 150,891 | |
| agree ACCEPT | 101,970 | 67.58 |
| agree REJECT | 42,621 | 28.25 |
| **jar-accepts / mettle-rejects (drop-in violations)** | **0** | **0.00** |
| jar-rejects / mettle-accepts (over-acceptance) | 6,300 | 4.18 |
| **agreement** | **144,591 / 150,891** | **95.82** |

mettle: 108,270 accept / 42,621 reject (parse-phase 14,671, resolve-phase 27,948,
load-phase 2), **0 panics**. The direction that matters for the drop-in promise —
**jar-accepts / mettle-rejects — is 0**.

### 3.3 The 6,300 over-acceptances, by jar reject class

| jar reject | count | disposition |
|---|---:|---|
| illegal relational join | 3,261 | documented — not tightenable (needs precise types) |
| ambiguous name (bare-name/field) | 1,505 | documented — ADR-0009 decision-3 outcome (see §5) |
| must be a formula expression | 503 | ambiguity-suppressed (enforced when unambiguous) |
| arity mismatch (`in`/`&`/`=`/`-`/`!in`/`!=`) | ~430 | ambiguity-suppressed (enforced when unambiguous) |
| incorrect function/predicate call | 188 | documented — relational fallback accepts |
| must be a unary set | 132 | documented — narrow structural, rare |
| must be a set or relation | 65 | ambiguity-suppressed |
| must be an integer expression | 39 | ambiguity-suppressed |
| multiplicity expression not allowed | 35 | documented — narrow structural, rare |
| exactly-of expression | 17 | documented — narrow structural, rare |
| `~`/`^`/`*` non-binary | ~19 | ambiguity-suppressed (enforced when unambiguous) |
| "failed to be typecheck", other | ~106 | mixed / long tail |

All measured frequencies are in [LIMITATIONS.md](../../LIMITATIONS.md).

## 4. Fixes shipped

Every fix drove the drop-in-violation count to **0** and/or closed an
over-acceptance class, each with a regression test in
`crates/als-types/tests/resolve_probes.rs` (suffix `_mt020`) whose accept/reject
verdict was independently jar-verified.

**Over-acceptance closers** (mettle used to *accept*; now rejects, as the jar
does) — the reference's `typecheck_as_{formula,int,set}` sort checks and the
`ExprUnary` binary-arity checks were entirely missing (the all-valid corpus never
exercised a reject path, so mt-018's 167/167 hid this). Added to `resolve/expr.rs`
(`typecheck`, `require_binary`) with new typed `ResolveError` variants
(`NotFormula`, `NotSet`, `NotInt`, `UnaryNotBinary`; `IllegalJoin` added to the
taxonomy but deferred, see §5):

- **set-as-formula** (`fact { A }`), **formula-as-set** (`some (A in A)`),
  **non-int comparison** (`A < A`) → `NotFormula`/`NotSet`/`NotInt`.
- **`~`/`^`/`*` on a non-binary operand** → `UnaryNotBinary`.
- All guarded by the accept-lean bias (`self.ambig` / error-typed operand), so
  they never fire on an ambiguity-tainted subtree.

**Drop-in-violation fixes** (mettle used to wrongly *reject*; now accepts, as the
jar does):

- **Subset-sig implicit `this`** — a field of a `sig D in Parent` fact resolved to
  the bare binary relation instead of `this.f`, causing a false arity mismatch.
  New `ResolvedWorld::sig_is_same_or_descendent` walks `in`/`=` parents (the
  reference's `Sig.isSameOrDescendentOf`) for the implicit-`this` visibility
  check. Test: `subset_sig_implicit_this_accepted_mt020`.
- **Field named like an auto-opened stdlib pred** — `t.pos` (field `pos` vs
  `util/integer` `pred pos`) committed to a vacuous pred call (the arg's
  error-type made `args_apply` match) and typed the result as a formula. Fixed by
  committing to a call only when the args *strictly* apply, else falling through
  to the relational (field-join) reading — mirroring the reference's `ExprChoice`
  keeping both readings. Test: `field_named_like_stdlib_pred_accepted_mt020`.
- **Overloaded call disambiguated by relevant type** — `prevs[…]` /
  `foo[a+b]` on the RHS of `in` narrows two same-named overloads by the pushed
  relevant type (the ADR-0009 decision-3 top-down retry, applied to *call*
  choices, where it is safe). Test:
  `overload_disambiguated_by_relevant_type_accepted_mt020`. (Probe 15's LHS-position
  ambiguity still rejects.)
- **Higher-order macro** — `interesting_not_axiom[some_pred]` (a macro receiving a
  callable by name) can't be faithfully type-checked by mettle's type-only param
  binding; its body is now resolved accept-lean (`expand_macro`). Fixed 5 corpus
  false-rejects. Test: `higher_order_macro_accepted_mt020`.

## 5. The ADR-0009 verdict — decision 3 fired; the data says **leave the accept-lean posture**

ADR-0009 decision 3: "if the alloy4fun differential shows
jar-rejects-ambiguous/mettle-accepts at any meaningful rate, mt-018's walk gains
the reference's full top-down retry-then-error pass for choice nodes." The gauge
measured that class at **~1,505 codes (1.0%)** — well over the trigger threshold,
so the tightening was **implemented and measured**.

**Outcome: the tightening is not viable on mettle's current type representation.**
Emitting the "ambiguous name" reject when >1 distinct-type candidate survives
min-weight + the relevant-type filter produced **28,402 jar-accepts/mettle-rejects**
(new drop-in violations) and rejected **75 valid corpus models**, while removing
only ~1,478 over-accepts — a catastrophic net loss. Root cause, exactly as
ADR-0009 anticipated: mettle's single fused pass carries only **coarse bounding
types**, so it *over-generates* candidates that the reference's precise top-down
retry (over precisely-typed candidates) would narrow to one. The choice-resolution
logic is not the blocker; the **type precision** is. The same defect sinks the
illegal-join tightening (3,436 false rejects vs 3,261 true catches, ~50/50 —
mettle's join type is spuriously empty on multi-hop joins).

Both tightenings were therefore reverted. The accept-lean posture stays, now
**measured** in LIMITATIONS. The genuine fix for both classes is precise
relevant-type propagation (a future bead), not a local `expr.rs` extension. Per
process, the ADR itself is not edited here — the tech lead records the outcome.

What *was* safely tightened: the call-ambiguity relevant-type narrowing (§4, the
RHS-of-`in` case), and the unambiguous sort/arity/binary-arity rejects (§4), none
of which depend on candidate over-generation.

## 6. Divergences documented, not fixed

Recorded in [LIMITATIONS.md](../../LIMITATIONS.md) with measured frequencies:
illegal joins (3,261), ambiguous names (1,505), ambiguity-suppressed sort/arity
(~1,000), incorrect calls (188), and three narrow structural classes
(unary-set 132, multiplicity-not-allowed 35, exactly-of 17) left as documented
rather than risk late regressions for <0.1%-each classes. Six codes are a
jar **parse**-phase reject that mettle accepts — the known "only `util/*` is
embedded" / lenient-lex tail (mt-013), negligible.

## 7. Definition-of-done check

- **Zero jar-accepts/mettle-rejects** over 150,891 alloy4fun codes **and** 167/167
  corpus — the drop-in gate holds.
- Over-acceptances measured, bucketed, and (where safe) closed; the rest
  documented with exact counts and rationale.
- ADR-0009 decision 3 fired and was resolved by measurement (§5).
- 0 panics across 150,891 in-process resolves.
- 9 new regression tests (`_mt020`), all jar-verified; full workspace gauntlet
  green (`cargo fmt --check`, `cargo clippy --workspace --all-targets -D warnings`,
  `cargo test --workspace`); corpus resolve stays 167/167.

## 8. Files touched

- `crates/als-conform/src/bin/resolve_gauge.rs` — new: the mettle-side batch driver + differential.
- `crates/als-conform/shim/ResolveGaugeShim.java` — new: real-path `resolveAll` verdict shim.
- `crates/als-conform/Cargo.toml` — the `resolve-gauge` bin + `als-types`/`als-syntax` deps.
- `crates/als-types/src/resolve/expr.rs` — sort/binary-arity enforcement, call strict-match & relevant-type disambiguation, higher-order-macro accept-lean.
- `crates/als-types/src/world.rs` — `sig_is_same_or_descendent` (subset-sig implicit `this`).
- `crates/als-types/src/error.rs` — new `ResolveError` variants (`NotFormula`/`NotSet`/`NotInt`/`UnaryNotBinary`/`IllegalJoin`).
- `crates/als-types/tests/resolve_probes.rs` — 9 `_mt020` regression tests.
- `LIMITATIONS.md`, `docs/README.md` — this doc linked in; measured divergences.
