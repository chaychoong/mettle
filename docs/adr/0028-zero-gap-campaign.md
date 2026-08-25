# ADR-0028 — The zero-gap campaign: the owner un-defers the whole correctness remainder

**Status:** Accepted (owner decision, 2026-08-25)
**Date:** 2026-08-25 · **Beads:** mt-126–mt-132 (new) + mt-107 (authorized, was owner-gated)
**Supersedes/amends:** [ADR-0024](0024-sig-metamodel-sized-defer.md) decision 1 (the `Sig$` feature defer — reversed), [ADR-0025](0025-over-accept-remainder-ranked.md) item 5 (the int-cast defer — lifted), and the "documented defer" posture on the mt-096 latent solve corners and the two cosmetic-parity residuals in [LIMITATIONS.md](../../LIMITATIONS.md).

## Context

After mt-125 every known gap was typed, priced, and parked: 4 alloy4fun over-accepts
(int-cast 3 + `Course$projects` 1), the 2 `Sig$` metamodel lowering rows, the mt-096
latent solve corners (zero corpus incidence, jar-SAT/mettle-UNSAT on synthetic
cells), and two cosmetic-parity residuals (the 059866.als warning line, the
documented XML/error-position shapes). Each was deferred on cost/benefit — the
owner's value function at the time.

On 2026-08-25 the owner changed that value function explicitly: **"I don't like
that there's still correctness gaps. Let's get them all out of the way."** Asked
per family, the owner put all four families in scope — including the `Sig$`
metamodel and the cosmetics — under a keep-going pacing grant. Cost/benefit
deferrals for correctness are therefore retired as a category; what remains
deferred must be deferred because it is *unpinnable*, not because it is
expensive.

Out of scope, unchanged: fullsub2[0] stays [ADR-0026](0026-compute-tail-sized-plan.md)'s
priced compute row (mettle defers honestly; the jar needed a 1800s tier to answer
the same row — a budget-pricing question, not a correctness one), and the
jar-parity rows (HO 4, temporal 2, jar_nonverdict 2) are already exact matches
of the jar's own behavior.

## Decision

Run the remainder as one campaign, quick known-design closes first, research-
and feature-shaped work behind them:

1. **mt-126 — the int-cast resolver slice** (ADR-0025 item 5, 3 codes). Probe
   wave pinning the jar's `smallIntType` push at `int[·]`/`sum` before any code;
   the known cliff (every `int x.f` routed through the broadest slice) is gated
   by the full 150,891-code resolve diff — **drop-in 0 or STOP**, probe tests
   land first (the mt-111 discipline for fixes that can create drop-in
   violations).
2. **mt-127 — re-key the int-compare gate on the jar's literal-cast test**
   (translation-ref §10.7e FACT 1: `EQUALS` int-compares only when both
   operands are literally `IntToExprCast`), then the `toInt` double-unwrap on
   top of it — the sequencing mt-096 measured as mandatory (the naive peephole
   moved the divergences instead of closing them: fixed n6/n7, broke n1/n2).
3. **mt-128 — the two known-design `ite_sort` corners**: thread a substitution
   environment so a `let`-bound int RHS reads as int (probe i23; the jar's
   `visit(ExprLet)` shape), and carry the resolver's `int[e]` → `Int[int[e]]`
   re-wrap marker so an `int[·]` ITE branch reads as a set (probe i8).
4. **mt-129 — the union/lone guard mechanism, probe wave with a genuine
   stop.** Three candidate rules have already been refuted by cells (LIMITATIONS
   §set-former-guard); no fix is attempted until a source/bytecode reading of
   the jar's overflow machinery plus discriminating cells pins the real rule.
   If the mechanism pins to something unimplementable-faithfully (e.g. cache
   visit order), that is the finding — it comes back here as a measured
   impossibility, not silence. **mt-130** (blocked on mt-129) implements
   whatever pins.
5. **mt-107 — the `Sig$` metamodel, authorized.** ADR-0024's alternative
   "build in full", exactly as sized there: P0 (the ~50-cell M1–M6 wave) with
   its **genuine stop** preserved — guard-behaviour or symmetry surprises
   re-size before P1 — then P1–P5. Closes the 2 sweep rows, the
   `Course$projects` over-accept, and retires the model-wide meta leniency
   (the 17 `lenient()` sites) at P2.
6. **mt-131 — warning-attribution parity**: an operator-token `Pos` distinct
   from the node `Span`, closing 059866.als and making warning parity
   101,970/101,970.
7. **mt-132 — cosmetics close-or-pin**: enumerate the documented XML-shape and
   error-position residuals; each either closes to byte-parity or gets a
   measured impossibility note. Nothing stays "cosmetic, unexamined".

Standing gates are unchanged and binding: probe-first for anything unpinned,
solve-touching changes sweep immediately (batched-sweep exemption), resolver
reject-direction changes diff against `baselines/alloy4fun-resolve.txt`,
double-run byte-identity where numbering can move, and each bead is its own
commit so a failing end-of-run sweep bisects cleanly.

## Consequences

- End state, if everything closes: solve agree 554/564 with every non-agreeing
  row jar-parity or ADR-0026-priced; alloy4fun over-accepts 0; warning parity
  exact; the latent-corner list empty or all-pinned-impossible; LIMITATIONS
  shrinks to honest capacity notes and deliberate better-than-reference
  divergences.
- ADR-0024's blast-radius warning transfers to mt-107 execution: the campaign's
  riskiest landings are the four pinned invariant families (atom order, bounds
  goldens, symmetry counting, XML), all gated behind P0's stop.
- The combined feature-complete review ([REVIEW-v0.1.0.md](../REVIEW-v0.1.0.md))
  remains the standing owner gate and is unaffected; this campaign runs ahead
  of it.
