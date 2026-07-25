# ADR-0013 — The verification instrument never trades coverage for speed

**Status:** Accepted (owner-decided 2026-07-25) · **Date:** 2026-07-25 ·
**Beads:** mt-057 (command-level parallelism; the skip lane built, measured and
deleted), mt-059 (baseline-before-enumerate), mt-058 (follow-up split)

## Context

The verification battery — stage-1 solve gauge plus both counting nets — had
grown to **~37 minutes**, and the mt-055 chunk spent ≈85 minutes of wall time
verifying a one-file lowering fix. Faced with that, there are two structurally
different ways to make the instrument faster, and they are **not**
interchangeable:

- **Skip work** — don't run commands whose answer we expect to be uninteresting
  (known over-budget, known non-comparable). Every second saved is a second of
  coverage given up.
- **Use the machine** — run the same work with better scheduling, or don't
  compute results that are discarded by construction. Nothing is given up.

mt-057 initially shipped the first kind: a committed sweep artifact plus a
"fast lane" that skipped 172 known-capacity commands. Measured on the full
corpus it saved **38% of CPU but only 8% of wall time**, because the real
bottleneck was that the unit of parallelism was the *file* and one file
(`correctChord.als`) was 556.5s of a 560s run — **1.18× effective parallelism
on ten cores**. Making the *command* the unit of work delivered 2.8× with
nothing skipped. Re-measured afterwards, the fast lane was worth **6%**.

Two hazards of the skipping approach were established concretely during review,
the first correcting a claim the tech lead had put in the spec:

1. **It can hide a genuinely wrong answer, not merely a missed gain.** A code
   change can make a previously-capped command newly solvable *and* answered
   incorrectly. Nothing regresses in the scorecard — there was no prior verdict
   to lose — so the instrument stays silent while mettle is newly wrong.
2. **It stops looking for panics and self-check failures** on exactly the
   largest, most pathological models, which is where they are most likely.

The owner's directive settled it: *"I just don't want to compromise on
correctness, but just do everything we can to speed things up."*

## Decision

**The gauge's default run always sweeps every command.** No coverage-reducing
mode is enabled by default, and none is used as a gate.

1. **Correctness-preserving optimizations are unrestricted** and belong on by
   default: parallelism and scheduling (command-level fan-out, LPT ordering),
   caching of *reference-side* facts (mt-054's jar count baselines), and
   **declining to compute results that are discarded by construction** — the
   mt-059 case, where the reference has no count to compare against, so no
   possible result could change the command's bucket. This last one is *not* a
   coverage trade: we are not choosing not to compare, the comparison does not
   exist.
2. **Coverage-reducing features are rejected by default** and must be
   re-measured *after* every correctness-preserving optimization has landed,
   because the latter can render the former worthless — as it did here (10
   minutes → 6%). Sunk implementation cost is never a reason to ship one; the
   mt-057 fast lane was deleted, not kept.
3. **Where a correctness-preserving change nonetheless lapses some exercise of
   a code path**, it gets an explicit opt-in that restores it, so the coverage
   is deliberate rather than silently lost. mt-059's `--enumerate-all` is the
   pattern: skipping non-comparable enumerations stops exercising the
   *incremental* enumerator (`block()` + retained learned clauses), so the flag
   exists to run it on purpose.
4. **The determinism contract is not negotiable for speed.** Byte-identical
   stdout at any job count remains the acceptance test for every change to the
   instrument (currently `c77ef8ce…` for stage 1). Reordering execution is
   allowed *only* because results fold by original position; any optimization
   that cannot preserve that is rejected.

## Consequences

- The battery went **~37 min → ~12 min** with zero coverage traded (stage-1
  10m09s → 3m36s, SB-0 net 14m06s → 3m45s, SB-20 net 12m53s → 4m33s), so the
  policy cost nothing in practice — the correctness-preserving levers were
  simply the larger ones all along.
- **What remains is a genuine floor.** The battery is now bounded by individual
  SAT solves (stage-1 by `correctChord.als[23]` at ~236s). Going further means
  either violating this ADR or optimizing the solver against the determinism
  contract — high risk, bounded payoff. The honest answer at that point is to
  stop; recorded at the end of the mt-059 bead.
- Committed artifacts that could rot are permitted **only** where their content
  cannot reach an answer. The sweep artifact supplies scheduling hints and
  `--delta` comparisons; a header mismatch is a hard error exactly when its
  content bears on the result (`--delta`) and an ignorable warning otherwise —
  a strict-always rule was tried and would have failed **every deep-budget
  sweep** the moment an artifact was committed.
- Diagnostic corollary, filed in [LESSONS.md](../LESSONS.md): all three
  bottlenecks this project has had (mt-054, mt-057, mt-059) were **discarded
  work or scheduling, never slow code**, and a CPU profiler would have said
  "time in SAT solving" every time. Instrument order is CPU÷wall against core
  count → per-item accounting → bucket the *output* and ask what is thrown
  away; a profiler only after those are clean, aimed at one deterministic
  command.

## Alternatives considered

- **Keep the fast lane as an opt-in flag.** Rejected: at 6% it is not worth a
  documented hazard, a code path, and the standing risk that someone reaches
  for it under time pressure and gates on it. Deleting it also removed the
  question of whether a given report is comparable to a full sweep.
- **Change-impact selection** (run only the commands a change could affect).
  Attractive, and unlike blanket skipping it *could* be sound — but only with a
  proven over-approximation of the affected set, which is real work with a real
  chance of being subtly wrong. Not attempted; the parallelism win made it
  unnecessary for now.
- **Solver optimization.** Deferred, not rejected. The determinism contract
  (no floats, no hashing near numbering, fixed VSIDS) rules out much standard
  SAT tuning, so the payoff must clear a high bar. mt-059's tail records the
  one measurement that would justify starting: the encode-vs-solve split on the
  slowest single command.
