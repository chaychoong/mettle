# ADR-0025 — The over-accept remainder, fully sized and ranked (the conformance endgame packet)

**Status:** Closed — the ranking packet is discharged: every item it ranked has shipped (mt-110, mt-111/[LEDGER-016](../../SEMANTICS_LEDGER.md), the [ADR-0023](0023-compound-operand-bidirectional-resolution.md) phases) or moved to its own decision ([ADR-0028](0028-zero-gap-campaign.md) amended item 5). The packet text below is unchanged.
**Date:** 2026-08-23 · **Bead:** mt-109 (sizing) · **Evidence:** `scratchpad/probe/mt109/{families-mechanism,mult-flag}.md` + 88 probe cells + a regenerated full jar verdict set; [ADR-0023](0023-compound-operand-bidirectional-resolution.md) (+ its two addenda), [ADR-0024](0024-sig-metamodel-sized-defer.md), [LEDGER-016](../../SEMANTICS_LEDGER.md).

## Context

After mt-108, the alloy4fun scorecard stands at 150,891 codes → 0 drop-in violations, **309 over-accepts**. This round decomposed the entire 309 by fresh measurement — the jar verdict side was regenerated in **~225 seconds** (`ResolveGaugeShim` batch over the full code list, cross-validated by reproducing 101,970/48,612/0/309 exactly), which retires a stale planning assumption: **resolve-phase jar sweeps are ~4 minutes, not an expensive gate** (the expensive sweeps are solve-phase). Per-code over-accept lists by jar reject class now exist again (session scratchpad, `jar_full.jsonl` + `over_buckets.json`).

## The measured decomposition (all numbers measured this round)

The ADR-0023 phase-(a) prototype (closure fix + un-truncation + nested-spine reach, rebuilt in an isolated repo copy) was run against the FULL gauge: **over-accepts 309 → 88, drop-in 0, corpus 167/167.** ADR-0023's own yield estimate was pessimistic — it closes **221**, not ~113, because the old "left-of-join type approximation ~94" family was mislabeled: 82 of its 85 codes are the same compound-right-operand mechanism (dominant shape `p.~projects` — a transpose over an ambiguous name in join-right position), and no code in that family has a function call in join-left position (mt-025's hypothesis refuted by data).

| # | item | codes | verdict | cost | owner-facing status |
|---|---|---:|---|---|---|
| 1 | **ADR-0023 phases (b)–(e)** | **221** | build | 5–7 d (unchanged) | **awaiting the owner's go** — yield now measured, not estimated |
| 2 | **Cheap resolver leniencies** (bare non-0-ary func as value 13 · `->` sort check 4 · bare `this` 2) | 19 | build | ~30 lines, 1 small bead | ▢ **mt-110, tech-lead-authorized** (no-fork; one-line jar-verified repros banked) |
| 3 | **`Pick::NoIntersect` fall-through** | 8 | build | inside ADR-0023 (d) | folded into (d) with the measured flip list |
| 4 | **Mult-flag family** ([LEDGER-016](../../SEMANTICS_LEDGER.md) — the rule is now fully pinned, 88 cells) | ~34–38 | build, batched | 2–3 d | ▢ **mt-111, tech-lead-authorized**, sequenced with the next sweep window; probe tests land FIRST (this is the one family whose fix can create drop-in violations — three pinned traps: fun bodies accept mult; quantifier-vs-comprehension asymmetry through one shared function; `in` asymmetry) |
| 5 | int-cast slice (`int x.f` pushes the operand's own type, not `smallIntType`) | 3 | **defer, documented** | ~10 lines but cliff-shaped risk | risk disproportionate to 3 codes |
| 6 | illegal-join under `*`-closure | 12 | **defer + probe question filed** | probe ~0.5 d first | whether the jar checks join legality on resolved vs make-time types — worth pinning if someone is already in this code for (d) |
| 7 | genuine grab-bag (incl. 2 declaration-order rejects that belong to the loader) | 9 | leave documented | — | six unrelated causes |

**End-state arithmetic:** ADR-0023(d) [→88] + mt-110 [−19] + mt-111 [−~34] + the (d)-folded 8 ⇒ **~25–30 residual over-accepts** across the deferred/documented tails — at which point every remaining code is individually understood, and further tightening is either cliff-shaped (5, 6) or unrelated one-offs (7). That is the honest floor of resolver conformance short of building the full metamodel (ADR-0024, recommended never).

## Decisions

1. **Rank as the table above.** ADR-0023 first (it now carries 221 of 309 + the last convertible solve row); mt-110 rides immediately after (or alongside — independent code paths); mt-111 lands its 88 probe tests first, then the check, batched into the same verification window.
2. **Cache the jar resolve verdicts as a committed baseline** (the mt-054 count-baseline pattern: config header + hard-error on mismatch), folded into mt-110's scope — every future resolver gate then diffs in seconds against a 4-minute-refreshable artifact.
3. **Correct the record:** ADR-0023's yield line and the mt-025 "left-of-join" family label are amended by this ADR + the ADR-0023 addendum; the sweep-cost assumption is retired in LESSONS.

## Consequences

- The owner's decision surface is now exactly three calls: **ADR-0023 go/no-go** (measured 221 + ertms_1A[5]), **ADR-0024/mt-107** (recommended never), and the standing compute-tail fork. Everything else is authorized tech-lead-scope work or documented defers.
- LIMITATIONS gains the three defer families with their mechanisms so none is re-derived a third time.

## Outcome, 2026-08-23: the packet's arithmetic landed

All four ranked items shipped same-day: **mt-108** narrowed the `seen_dollar`
gate (314 → 309), **mt-110** closed the 19 cheap leniencies (309 → 290),
**mt-111** shipped LEDGER-016 (290 → 252), and **ADR-0023 phases (b)–(d)**
(mt-105) closed the compound-right-operand family (252 → **27**), 0 drop-in
throughout every step. The residual 27 is decomposed per-code at
[reference/alloy4fun-resolve-pass.md](../reference/alloy4fun-resolve-pass.md)
§12 and `scratchpad/probe/mt105e/decomposition.md` (banked); the family
totals against this ADR's items:

- **Item 6, illegal-join under `*`-closure — predicted 12, measured 10, and
  the mechanism is narrower than the label.** Of the 10 residual: 7 are the
  predicted `*`/`^` closure shape; 2 are a plain variable quantified
  directly over `univ` reaching the same `IllegalJoin`-suppression guard
  (not a `*` at all, but the identical guard); 1 (`Course$projects`) is a
  **different** mechanism entirely — a genuine `S$f` meta-field name the
  mt-108-narrowed gate correctly recognizes but cannot fully resolve, owned
  by the deferred `Sig$` metamodel (mt-107), not by the `IllegalJoin` guard.
  The open probe question (resolved-vs-make-time join legality) stays filed
  against the 9 `univ`-triggered codes; it does not apply to the
  `$`-triggered one. **Answered later the same day by the mt-112 probe wave
  (24 cells, 23/24 predictions held): the check is a make-time ARITY rule —
  result arity < 1 rejects, arity-legal-but-empty joins accept with only a
  warning — and `univ` is a genuine unary type with no special casing. The
  merged-vs-resolved halves of the question are observationally equal (the
  candidate-union typing means no reachable program separates them). A
  measured prototype closes the 9 with 0 drop-in (27 → 18); the fix is
  owner-gated as mt-113. Record: TASKS ✔ mt-112,
  `scratchpad/probe/mt112/`.**
- **Item 5, int-cast slice — predicted 3, measured 3, unchanged.** Still the
  documented defer: cliff-shaped risk (every `int x.f` would route through
  the broadest slice) against a 3-code yield.
- **Item 7, grab-bag — predicted 9, 6 remain (measured), the other 3 closed
  unpredicted.** Of the original 9 (mt-109 §3.6: 3 name-not-found misc, 2
  declaration-order, 1 `Subset abstract`, 1 `set-of`-adjacent mult, 1
  failed-to-typecheck residue, 1 `Ad.p`/`iden` illegal-join misc): 1
  (`Ad.p`/`iden`) is now correctly re-bucketed under item 6's illegal-join
  family rather than left as grab-bag, leaving 5 measured in the current 27
  (2 declaration-order, 1 `Subset abstract`, 2 of the 3 name-not-found
  one-offs). The remaining 3 of the original 9 — the third name-not-found
  code, the `set-of`-adjacent mult code, and the failed-to-typecheck residue
  — closed, matching the phase-(d) commit's own "3 grab-bag" count among its
  offsetting unpredicted closes; which specific codes is not independently
  traceable, since mt-109 sized this family by jar-reject-class count from a
  fresh sweep, not a preserved per-code list.
- **Item 6's 12→10 delta (the "2 bonus defer closes") is likewise not
  individually traceable for the same reason** — mt-109's illegal-join
  count came from a class-level jar tally, not a banked code list, so which
  2 of the originally-estimated 12 converted cannot be recovered after the
  fact. What is measured directly, from the current 27: the residual 10 is
  narrower than the label suggests — see item 6 above.
- **A new family this ADR did not predict: `Pick::NoneArity`, 8 codes.**
  Item 3 (folded into ADR-0023 phase (d) as the `Pick::NoIntersect`
  fall-through, 8 codes, `projects.projects` shape) turned out to be the
  wrong mechanism — the codes exit at a distinct `Pick::NoneArity` collapse
  one rung earlier, not the `NameNotRelevant` arm phase (d) built for them.
  **Correction to mt-109 §3.2 (and anywhere it is cited from this ADR): the
  attribution is wrong — read "8 `Pick::NoneArity` codes", not
  "`Pick::NoIntersect`".** The 8 codes still ship inside phase (d)'s scope
  as claimed; only the arm that would have closed them was the wrong one.
  Now its own documented residual family (LIMITATIONS.md,
  reference-doc §12.4).

**Net:** every item this ADR ranked was acted on the same day it was
authorized, and the honest floor it forecast (~25–30 residual, each
individually understood) landed almost exactly at 27.
