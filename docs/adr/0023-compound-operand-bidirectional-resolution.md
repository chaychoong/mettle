# ADR-0023 — Bidirectional resolution into compound join operands (the "ExprChoice" thread, sized)

**Status:** Proposed — implementation awaits the owner's cost/benefit call (phases (b)–(e) below); phase (a) is probe-only validation.
**Date:** 2026-08-22 · **Bead:** mt-104 (sizing) → mt-105 (implementation, gated)
**Depends on:** mt-102 (the probe round that pinned the behaviour), mt-025 (the materialized two-pass structure this extends), mt-040 (the `ChoiceTable` seam lowering consumes)
**Amends:** [ADR-0009](0009-fused-resolve-pass-accept-lean.md) — the compound-right-operand clause of the accept-lean posture only; the rest of that posture stands.
**Evidence:** `scratchpad/probe/mt104/{design,effect-estimate}.md` (git-ignored, banked), `scratchpad/probe/mt102/` (27 one-cell jar probes). This ADR is self-contained; the memos carry the working detail.

## Context

mettle's resolver is a faithful port of Alloy 6.2.0's `resolveAll` with one deliberate leniency: a JOIN's **compound** right operand (`t.*next`, `x.(y.z)`) keeps its bottom-up type for the verdict; any errors from resolving it are truncated (`resolve/expr.rs:2726-2730`), and a nested-spine right operand is only re-resolved by the recording side-pass against its own bottom-up type (`record_operand`, `expr.rs:372-379`). mt-025 measured the naive alternative — resolving the compound standalone — at **28,402 false rejects**, so the leniency stayed (ADR-0009).

Two live costs today:

1. **ertms_1A[5]** — the last convertible stage-1 sweep row. `ertms_1A.als:1036` is `tr1.MA.(t6.*next) = V/last` under three `util/ordering` opens; the jar type-checks it, mettle accepts it too but **defers at lowering** because the ambiguous `next` never gets a `ChoiceTable` entry (the recording pass filters against `*next`'s own type `univ->univ`, which excludes nothing).
2. **118 of the 314 alloy4fun over-accepts** — the compound-right-operand family ("name cannot be found" 61 + non-binary `*`/`^`/`~` 57, exact counts re-derived from the mt-025 §10.3 table net of mt-026's 6 parser codes).

mt-102 refuted the original "thread the join's left-slice type" premise and concluded the jar runs `ExprChoice` bidirectional resolution — a candidate set carried bottom-up, filtered top-down — calling it a subsystem. **This sizing revises that conclusion's implementation half while keeping its behavioural half.** The observable is exactly as mt-102 pinned it; but the reference does **not** distribute candidate sets through compound operators — `ExprUnary.Op.make` builds an ordinary node over a child `ExprChoice` and keeps the *merged* type; disambiguation happens later when `ExprUnary.resolve`/`ExprBinary.resolve` push a narrowed relevant type down and the choice node's `resolveHelper` filters (precisely the stack trace mt-102 observed, and why the jar's error prints the *post-filter* candidate list). mettle already owns both halves of that mechanism: `Cx::infer` performs the bottom-up merge (`infer_name`'s merge *is* `ExprChoice.make`), and `pick_name`/`pick_reading` → `resolve_helper` *is* the top-down filter. What's missing is narrower: **the relevant type never reaches the choice node in two positions.**

## The two gaps (both verified against the code)

- **G1 — the closure arm approximates.** `unary_r`'s `Closure`/`ReflexiveClosure` arm (`expr.rs:988-1021`) pushes `subt.extract(2)` — the operand's *own* binary shape — instead of the reference's `resolveClosure(p, sub.type)`. For an ambiguous `next` that is the full 4-way merge, so the filter excludes nothing. The faithful `resolve_closure` **already exists and is faithful** (`expr.rs:3052-3135`) but is only used for the A2 warning (`:1055`). The mt-035 recording-only retry (`:1014-1021`) uses `p.extract(2)` — closer, but still not the faithful narrowing, and its errors/warnings are truncated.
- **G2 — the relevant type never arrives at a compound right operand.** In `finalize_reading`'s `Fin::Join` arm the compound is resolved against the correct slice `bp` but with errors truncated (`:2726-2730`); a nested-spine right operand isn't resolved in place at all (`right_expr: None`, `:2306-2309`) — only `record_operand` sees it, against the wrong (bottom-up) type.

## The derivation — all 13 mt-102 cells from G1+G2 alone

The deciding quantity per cell is the relevant type pushed to the choice at `next`: `resolve_closure(bp, merge)` where `bp` is the join's right slice from `join_slices` (`expr.rs:2800-2867`). The load-bearing asymmetry: `*` types as `univ->univ` (`:1034-1038`) while `^` keeps the merge's closure — so `t.*X : univ` but `t.^X : Time`.

| cell | relevant type reaching `next` | survivors | jar | derived |
|---|---|---|---|---|
| v01/x01/x03 `tr.MA.(t.*next)` | `Time->Time` | T/next | OK | ✓ |
| x05 `tr.MA.((v.(tr.MA)).*next)` — left types **Time** | `Time->Time` | T/next | OK | ✓ |
| x02 `tr.MA.((t.*T/next).*next)` — left types **univ** (`*` ⇒ `univ->univ`) | `univ->Time` | all 4 | REJECT | ✓ |
| w04/w05/w06 (`^`, `~`, `next+next`) | `Time->Time` | T/next | OK | ✓ |
| w09/v06 `some (t.*next)` — `some` pushes the operand's own type | reaches all | all 4 | REJECT | ✓ |
| w02 `some (x.*next)`, `x: Train` | reaches all | all 4 | REJECT | ✓ |
| w10 `(t.*next) = t2` — `=` intersects ⇒ Time | `Time->Time` | T/next | OK | ✓ |
| w11 `(t.*next) in Time` — `in` keeps left's own type ⇒ univ | reaches all | all 4 | REJECT | ✓ |
| w07/w08 orderings on `sig B extends A` — `resolve_closure` links A↔B by reachability | both | 2 | REJECT | ✓ |

All three of mt-102's refutations are reproduced: x02 vs x05 differ by the left operand's *type* (univ vs Time), not any left-slice rule; w07/w08 reject via closure reachability across the sig hierarchy; w10 vs w11 differ because `=` and `in` compute different relevant types for their left child. **Caveat, stated plainly: this is a hand-computed paper trace** against verified jar verdicts and verified mettle code — phase (a) below executes it before anything ships, and a single disagreeing cell is a stop (the full candidate-set port comes back on the table).

## Design (summary; full detail in the banked memo)

1. **No new candidate-set type.** Candidate sets stay where they already live — `Vec<Cand>` at bare names (`pick_name`), `Vec<Reading>` at application spines (`pick_reading`) — and every other node carries the merged `Type`, as the reference does. One structural unification: `Cand` and `Reading` become one struct, and `Fin::Join` carries the chosen base candidate (`base: Box<Cand>`) instead of a shadow of it, which deletes `RecNode`/`flush_rec`/`rec_of`/`record_operand` (~net-negative code).
2. **Bottom-up pass unchanged.** No `infer` arm changes; compounds keep collapsing to one reading whose type is the merge (|L|+|R| cost, no products).
3. **Top-down filter — two real edits.** (i) The closure arm pushes `resolve_closure(p, subt)` (with the arm's existing `has_entries` fallback shape), deleting the mt-035 retry. (ii) `Fin::Join` resolves the right operand *in place* through the chosen candidate against `bp`, recursively, keeping errors — recording thereby moves onto the verdict path (a recorded choice is by construction one the verdict agreed with; that's what closes ertms_1A[5]). `join_slices`, `compare`'s `=`/`in` slices, quantifier pushes, `Transpose`, `resolve_helper`, `resolve_closure` are already faithful and **must not change** — the derivation depends on each staying exactly as it is.
4. **The ADR-0009 leniency:** the global accept-lean posture (lenient `$`-meta, ambiguity arms, univ guards) survives untouched; the compound-right-operand clause specifically is subsumed and deleted. **Why the 28,402-cliff does not re-open:** the cliff was caused by filtering against the compound's *own* bottom-up type (`univ->univ` for `*next` — excludes nothing, rejects every ordering model). The new pass never computes a filter from the node itself; `bp` comes from the join context and `resolve_closure` narrows further by reachability. Operationally, fixing G1 *before* un-truncating G2 is the difference between a tightening and a cliff — hence the phase split. A `slice_precise` valve (thread a Block-1-vs-fallback bit out of `join_slices`; errors under imprecise slices stay truncated initially) is the measurement instrument if the gauge finds residual false rejects; it ships only if the numbers demand it.
5. **Determinism:** zero `HashMap`/`HashSet` in `resolve/` (grep-verified); candidate order is the §4.4 scope chain in `Vec` order, preserved by `retain`; left-before-base resolution order pinned for warning parity; no new tie-breaks.

## Measured effect estimate (provenance in the banked memo)

Grounding: no cached jar verdicts survive on disk, so per-class counts are prose-derived from mt-025 §10.3 — but the **314 total was independently reconfirmed today by arithmetic** against a fresh mettle-side gauge run (16.0s wall, 150,891 codes, byte-identical to the mt-103 checkpoint sha `78f43b09…`; accepts 102,284 = 101,970 + 314 exactly, parse-rejects +6 = exactly the mt-026 codes).

| family | count | closed by this design? |
|---|---:|---|
| 1. compound right operand (name-not-found 61 + non-binary 57) | **118** | **fully — the direct target** |
| 2. deep left-of-join ambiguity | 94 | **no** — a left-side type-*approximation* defect (un-specializable returns); mt-102's w07/w08 confirm independently that right-side candidate handling can't fix a left-side precision problem |
| 3. multiplicity flag (mult 25 + exactly-of 13) | 38 | no — `mult` flag untracked, orthogonal |
| 4. residual (illegal join 21, incorrect call 22, sort checks 7, mixed 14) | 64 | no — separate join-type/call-precision defects; zero credit until proven otherwise |

**Headline: ~118 of 314 over-accepts close (37.6%), plus ertms_1A[5] on the solve gauge** — the last convertible stage-1 sweep row, which the headline undercounts. The other 196 need three unrelated fixes and are **not** bundled here.

## Byte-identity risk

The catastrophic direction is a currently-agreeing code flipping to mettle-reject/jar-accept (0 today). Measured exposure (crude, grep-level over the fresh code dump): **63 currently-accepted codes** contain a closure operator directly over `next`/`prev`/`first`/`last` — the exact pinned ambiguity shape (45,000 codes open `util/ordering` at all, but only 3 open it more than once; the closure-shape narrowing is what gates real exposure). Some of those 63 are intended flips (the jar rejects them today); the accept/keep split **is** the implementation's byte-identity gate and requires one full jar sweep before merge — a one-time JVM cost deliberately not spent during sizing. Structural reasons this is lower-risk than ADR-0009's failed tightening: that attempt lacked the type-precision infrastructure mt-022/025 have since built, and filtered against the wrong (self) type by construction; and mt-102's 15 probe cells are a ready-made jar-verified regression suite in both directions. Second-order risks gated per phase: warning parity (the truncated passes currently discard warnings too) and gauge wall time (16.0s baseline pinned).

## Incremental plan (phases of bead mt-105; (b)–(e) owner-gated)

- **(a) Validate the derivation — probe-only, no shipped change.** Instrument the closure arm + join finalize (throwaway), run the 27 mt-102 cells, confirm the derivation table cell by cell. **Gate: 13/13 or stop.** ~0.5 day, opus.
- **(b) Faithful closure operand type** (G1). One arm, ~15 lines net negative. Gates: resolve gauge 0 new drop-in over 150,891; over-accepts move only within the closure family; warning parity; corpus 167/167. ~1 day, opus.
- **(c) Carry the chosen base; recording moves onto the verdict path** (G2 structure, errors still truncated ⇒ verdict-neutral by construction). Gates: resolve gauge **byte-identical** (sha256); **stage-1 sweep row-diff exactly `ertms_1A[5]`** — this phase alone closes the ertms gate. ~2–3 days, opus.
- **(d) Un-truncate; the over-accept family closes.** Add `ResolveError::NameNotRelevant` for the newly-reachable no-intersect path. Gates (hard): **0 jar-accepts/mettle-rejects over 150,891** (fresh jar sweep — the one-time JVM cost lives here); over-accepts fall by ≤118; six jar-REJECT probe cells become mettle rejects with x05/v01 as live negative space. ~1–2 days + gauge runtime, opus.
- **(e) Docs.** LIMITATIONS rewrite (lines 31/68 families), resolve-pass §11 before/after, ADR-0009 amendment, this ADR → Accepted. ~0.5 day, sonnet.

Total ~5–7 agent-days, hard chain (a)→(b)→(c)→(d), no useful parallelism.

## Alternatives considered

- **A. Full candidate-set port** (mt-102's stated conclusion): a `CandSet` threaded bottom-up with distributing arms for every compound operator. Rejected: the reference itself doesn't do it (§Context); it costs |L|×|R| on `t.(next+next)` where the reference costs |L|+|R|; and the post-filter error list the jar prints is what filtering at one choice node produces. All 13 cells are explained without it. It returns to the table only if phase (a) fails.
- **B. Recording-only slice threading** (~30 lines, closes ertms, zero verdict risk). Rejected as a *design*: the recorded choice would come from a path the verdict never validates — the exact failure mode mt-031's "record at the decision point" rule prevents. Stopping after phase (c) strictly dominates it as a fallback position.
- **C. Do nothing.** Over-accepts don't violate the drop-in gate. Rejected narrowly: ertms_1A[5] is the last convertible sweep row and its fix is the same structural work; doing the structure and skipping the tightening would be the odd choice.

## Recommendation

Take the design above — faithful top-down resolution into compound operands, no candidate-set port. Sequence (a)→(e) with (a)'s gate as a genuine stop. The owner decision requested: authorize mt-105 phases (b)–(e) (~5–7 agent-days, two hard gates, one full jar sweep at (d)) against the measured payoff (118 of 314 over-accepts + the last convertible sweep row).

## Addendum — phase (a) EXECUTED, 2026-08-22 (same day): the derivation is now observed fact

Phase (a) ran to completion on a throwaway instrumented tree (env-gated dumps + a crude two-step prototype of edits (a)+(b); everything reverted, `git status` clean, build re-verified; full record `scratchpad/probe/mt104/phase-a.md`). Results, all in the design's favor:

- **13/13 derivation rows confirmed by direct observation** — every predicted slice was read off the dumps, not inferred, including the crux asymmetry (x02's inner left really types `univ` vs x05's `Time`) and w07's post-filter candidate list matching the jar's exactly (`integer/next` dropped by `resolve_closure` reachability, two ordering candidates remain). **Risk 1 ("the derivation is hand-computed") is retired.**
- **25/25 cell verdicts match the jar under the prototype** — all six predicted flips fired (plus v08/w03, two previously-unpinned cells, freshly jar-probed as REJECTs and correctly flipped); every jar-OK cell stayed accepted. The pre-fix dumps also show the 28,402-cliff mechanism verbatim: `record_operand` filters `*next` against `p={univ->univ}` and `resolve_closure(univ->univ, merge) = merge` — a perfect closure arm filters nothing when the arriving type is the node's own.
- **The phase split is calibrated correctly:** under the closure fix alone (phase (b) prototype) v01 still defers at lowering; with the join-slice threading (phase (c) prototype) `mettle exec v01` → SAT. ertms_1A[5] needs (c), with (b) as prerequisite — as the plan assumed.
- **Corpus canary 167/167 — after catching one prototype defect that becomes a BINDING phase-(c) review invariant.** The first crude spike re-resolved a box-join's right operand **by `ExprId`**, re-running candidate selection, and wrongly rejected `lc-lenses.als` (three sigs each declaring a field `dist`; jar OK — a genuine drop-in violation). The design does not do this: `Fin::Join` carries the **already-chosen** `base: Box<Cand>` and finalizes it, so re-picking is structurally impossible. Restricting the prototype to the design's shape restored 167/167 with all cells unchanged. Phase (c)'s review must check exactly this invariant — *the right operand is finalized through the chosen `Cand`, never re-resolved by `ExprId`* — and `lc-lenses.als` is a required regression test.
- **Plan adjustments from observation:** the `slice_precise` valve has no supporting evidence (every cell's slice came from `join_slices` Block 1) — build it only if phase (d)'s gauge produces drop-in violations, not pre-emptively. The mt-035 recording-only retry is visibly redundant under the fix (dumps show the duplicate walk reaching the same answer) — deleting it in (b) is safe. `AmbiguousName`'s candidate list is carried but never rendered by the CLI — fold the renderer into phase (d) alongside `NameNotRelevant`.

Status stays **Proposed**; the owner ask is unchanged but the residual risk is now concentrated in phase (d)'s jar sweep, with phases (a)–(c) de-risked by execution.

## Addendum 2 — mt-109 measured the full yield, 2026-08-23: 221 of 309, not ~113

The mt-109 sizing round rebuilt the phase-(a) prototype in an isolated repo copy and ran the FULL 150,891-code gauge against a freshly regenerated jar verdict set (~4 min — the "expensive jar sweep" assumption was stale; see LESSONS): **over-accepts 309 → 88, drop-in 0, corpus 167/167.** The old "left-of-join type approximation ~94" family was mislabeled — 82 of its 85 codes are this ADR's own compound-right-operand mechanism (dominant shape `p.~projects`) and close here; no code in that family has a function call in join-left position. So this ADR's measured yield is **221 over-accepts + ertms_1A[5]**, and phase (d)'s expected-delta gate becomes "over-accepts fall to ≈88" (re-measure with the real implementation — the prototype reaches nested spines by `ExprId` re-resolution, which the design replaces with the chosen-`Cand` finalization; treat 88 as high-confidence, not a contract). Phase (d) also inherits a measured flip list for its `NameNotRelevant` arm: 8 `Pick::NoIntersect` fall-through codes (`projects.projects` shape) — implement the arm against that list, not speculatively. Ranking context: [ADR-0025](0025-over-accept-remainder-ranked.md).
