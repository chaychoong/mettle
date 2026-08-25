# ADR-0024 — The `Sig$` metamodel thread, sized: defer the feature pinned; narrow the `seen_dollar` stopgap now

**Status:** Proposed — the feature question (build vs stay pinned) is the owner's, packaged here alongside [ADR-0023](0023-compound-operand-bidirectional-resolution.md) so both named threads are decided from one packet. The stopgap narrowing (mt-108) is a no-fork conformance tightening the tech lead authorizes under the standing Option-B delegation, independent of the feature call.
**Date:** 2026-08-23 · **Bead:** mt-106 (sizing) → mt-107 (feature, owner-gated) + mt-108 (stopgap narrowing, authorized)
**Evidence:** `scratchpad/probe/mt106/sig-meta-design.md` (the full memo), `scratchpad/probe/mt097/a_meta*` (7 jar-verified probe cells), and a reference-source reading of `resolveMeta`/the quantifier ground-expansion (pinned commit `794226dd` — the mt-016 source-pinning practice; clean-room applies to stdlib text only, per ADR-0006).

## Context

The stage-1 sweep's 3 residual `lowering` rows split 1 + 2: ertms_1A[5] (sized, ADR-0023) and the **`Sig$` metamodel** pair — hc7[0] (`Vertex$.subfields`) and einstein-wikipedia[0] (`House$.subfields`), Alloy's reflection feature (`$`-suffixed meta-sigs exposing a model's own structure to quantification). mettle declines both with a typed defer, never a wrong answer. Today's accommodation is a **model-wide accept-lean switch**: `ModuleGraph::seen_dollar` (`als-types/src/graph.rs:116`) fires if any name leaf in any loaded file contains `$` (`load.rs:415-427`) and then suppresses expression-level rejection across the whole resolver — 14 `Cx::lenient()` guard sites plus 3 direct reads in `resolve/expr.rs`.

## What the sizing established

**The mechanism is now source-pinned, not guessed** (this round's reading of `resolveMeta` + `Context.visit(ExprQt)`; mt-097's "unpinned" list mostly dissolved):

- Meta sigs are ordinary **`one`-sigs** (`S$` under an abstract `sig$`; `S$f` per field under `field$`), and every meta relation (`value`, `fields`, `parent`, `subfields`) is a **defined (`=`) field** whose definition is the concrete sig/field relation — machinery mettle already has.
- The quantifier works by **resolve-time ground expansion**: `all f: Vertex$.subfields | …` is rewritten into a fold of the body re-resolved once per meta atom with `f` bound to that concrete singleton sig — so `f.value` is never higher-order; mt-097's "substitute at lowering" requirement is satisfied structurally by rebinding before resolution. This kills the presumed-hardest sub-problem but creates the actual crux: mettle's resolver is non-rewriting and its `ChoiceTable` keys one entry per `(ModuleId, ExprId)`; N bindings of one body node need **N sibling nested choice sub-tables** plus a lowerer that folds their replays (precedented shape: `MacroCheck::body_choices`; the sibling-multiplicity is new). If that seam doesn't take cleanly, the estimate roughly doubles.
- A ~50-cell probe wave (6 groups) would still be owed before building: meta vocabulary, the expansion guard's negative space, universe/XML atom order (`meta="yes"` becomes reachable — re-opens an mt-071 cell recorded as unreachable), symmetry/counting behaviour of the exact-bounded meta singletons, feature interactions (temporal/enum/ordering/REPL), and the `seenDollar` trigger's own negative space.

**Blast radius if built:** lands on mt-029 byte-identical atom order, mt-030 bounds goldens, mt-048/055 symmetry counting, and mt-071 XML simultaneously (contained to `$`-models by gating, but those invariants are the project's most carefully pinned). One item is already answered: meta atoms DO join mt-053's live `univ` (probe a6).

**Payoff, measured honestly:** 2 sweep rows of 564. Corpus incidence: exactly the 2 known files (of 9 `$`-containing files, 7 are comment-only). **alloy4fun incidence: 0 genuine metamodel uses in 150,891 codes** (7 `$`-containing codes, all inspected — stray characters in ordinary expressions). The reference itself gates the feature behind `Version.experimental`. **Cost: ~9–13 agent-days** (P0 probe wave → P1 synthesis pass + two `world.rs` widenings → P2 resolver expansion + retiring the 17 leniency sites → P3 lowerer replay-fold arm → P4 scope/bounds/XML parity → P5 gates), hard chain, versus ADR-0023's 5–7 days for 118 over-accepts + 1 row.

**The side-finding that IS worth acting on:** those 7 stray-`$` alloy4fun codes were run against the jar directly — **the jar rejects 7/7; mettle rejects 1/7**. So 6 of the 314 known over-accepts are caused by the *stopgap*, not the missing feature: a stray `$` anywhere in a file currently disables expression-level rejection for that entire file. (Bonus datum from one of them: the jar resolves `Course$projects` as a name of type `{this/Course$projects}` — independent confirmation that meta-field sigs are referenceable by their `S$f` spelling.)

## Decision (recommended)

1. **The feature: defer-pinned (Alternative D).** ~9–13 days landing on four pinned invariant families to convert 2 rows used by zero real-world submissions is the worst cost/benefit on the board; every comparable thread buys more per day. The rows stay honest typed defers; this ADR + the banked memo + the source reading mean a future build starts from a pinned design, not a blank page. If the owner wants the rows closed anyway (the drop-in North Star is a legitimate reason), the sequencing is P0→P5 with a genuine stop after P0 (guard-behaviour or symmetry surprises ⇒ re-size before P1).
2. **The stopgap: narrow it now (Alternative B, bead mt-108, authorized).** Replace the file-wide `seen_dollar` gate with one that fires only on plausibly-meta names — the `sig$`/`field$` builtins, and `X$` / `X$f` where `X` names a real sig — so `$Professor`-style strays take the ordinary reject path. Expected effect: over-accepts 314 → 308; the 2 corpus meta models keep resolving leniently (corpus stays 167/167); the 2 sweep rows keep deferring exactly as today. **Gates:** the mettle-side resolve-gauge diff must be exactly ⊆ the 7 identified stray-`$` codes (any wider diff = STOP); each flipped code carries its already-measured jar-reject verdict; corpus 167/167; the two meta models' sweeps byte-identical. No full jar sweep needed — the flip set is grep-enumerable and already jar-verified.

## Alternatives considered

- **Build it in full** — rejected on cost/benefit (above); remains available to the owner as mt-107 with the P0 stop.
- **Partial build (a1–a7 surface only)** — rejected: the atoms enter the universe either way, so the expensive invariant-touching part (P4) is unchanged; saves ~1.5 of 11 days and ships a wrong-on-anything-else metamodel that would be redone.
- **Do nothing at all** — rejected narrowly: leaves 6 measured over-accepts caused by our own stopgap, closable in ~half a day with grep-enumerable risk.

## Addendum — mt-108 SHIPPED, 2026-08-23 (same day): measured closure is 5, not 6

The narrowing shipped as designed (`ModuleGraph::dollar_names` collected at load; `Resolver::compute_meta_gate` decides once sig/field labels exist; `Cx::lenient` reads it; the `X$f` form requires `f` declared by `X` itself — the faithful shape, since an inherited field's meta sig sits under its owner). **Measured over all 150,891 codes (full pre/post mettle-side diff, independently re-verified by the tech lead): exactly 5 codes flip, all accept → reject `UnknownName`, each matching the jar's own reject at the same line and column. Over-accepts 314 → 309; corpus 167/167; the two meta models and all 7 mt-097 probe cells byte-identical in behavior.** The estimate's sixth code (060669, `Course$projects`) stays lenient, correctly — `Course` declares `projects`, so it is a genuine meta name (the jar's own error prints the resolved meta-sig type `{this/Course$projects}` before rejecting on the join shape); its over-accept is attributable to the missing feature (mt-107), not the stopgap, and this ADR's "6 caused by the stopgap" over-attributed by one. Deliberate posture pin: the narrowed gate stays model-wide, as the reference's `seenDollar` is — one genuine meta name still leniences the whole model (test-pinned so it reads as a decision, not a hole). Full record: `scratchpad/probe/mt106/mt108-report.md`, reference-doc §11 (alloy4fun-resolve-pass.md).

## Addendum — P0 EXECUTED, 2026-08-25 (mt-107 authorized by [ADR-0028](0028-zero-gap-campaign.md)): PROCEED to P1, sizing stands

The ~50-cell wave ran at 140 cells (`scratchpad/probe/mt107/`, predictions
first, all jar-verified). Both named stop-gates are clear: the expansion guard
matched the source reading on all 48 M2 cells, and meta atoms perturb no
symmetry count (24 of 24 counts identical with and without them). Atom order
is a clean append (root user atoms, then all `S$`, then all `S$f`, then
opened-module atoms; labels `A$$0` / `A$r$0`).

The wave's one major surprise: the four meta relation names (`value`, `fields`,
`parent`, `subfields`) are one field per meta sig, so they are N-way ambiguous
and the jar rejects with its ambiguous-name error whenever narrowing cannot
pick a single non-empty candidate (16 of 140 cells). The wave priced this as a
dependency on unbuilt ExprChoice work; that premise was stale. ADR-0023 and
the mt-115 ambiguity retry shipped on 2026-08-23, so the machinery exists and
meta fields route through it as ordinary same-named fields. The estimate
therefore stays at the original ~9–13 days. Tech-lead decision under the
standing Option-B delegation: proceed to P1.

Design amendments a builder must carry (full detail in the wave notes):
meta names are body-only (phase 8 runs after all declaration phases, so
expansion never crosses a `pred` boundary and the relation-valued-parameter
worry is gone); `meta="yes"` appears on sigs and fields in the XML, which
re-opens mt-071's X-03 cell for P4; `enum` and `util/ordering` mint their own
meta families; builtins (`Int$`, `String$`, `univ$`, `none$`) reject; the
reference copies its inconsistent var-inheritance halves (bucket `S$f` by
field variability, declare its `value` by sig variability) and mettle copies
both.

## Consequences

- LIMITATIONS' `Sig$` entry gains the sizing pointer; the `seen_dollar` leniency description changes when mt-108 lands.
- The owner decision packet is now complete across both named threads: ExprChoice (ADR-0023: recommend build, 5–7 days, 118 over-accepts + the last convertible row) vs Sig$ (this ADR: recommend defer, 9–13 days, 2 rows) — opposite recommendations, both from measured payoff.
