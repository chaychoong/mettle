# ADR-0002 — Conformance oracle & yardstick

**Status:** Accepted
**Date:** 2026-07-15

## Context
mettle's North Star is being a drop-in replacement for the latest Alloy, measured by conformance with the reference implementation. That requires pinning *what* we compare against and *what* comparison is actually canonical. Not everything the jar produces is a sound oracle.

## Decision
1. **The yardstick is a single pinned reference jar: the latest stable Alloy 6 release.** Pinned: **v6.2.0** (tag `v6.2.0`, jar `org.alloytools.alloy.dist.jar`, SHA-256 `6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d`). Full provenance, licenses, and empirically-verified headless invocation (verdict, count, `symmetryBreaking=0`, overflow default, SAT4J-only) are recorded in [reference/alloy6-reference.md](../reference/alloy6-reference.md) and treated as *the* oracle. Any other Alloy version is out of scope for conformance. Note: the CLI's `-y`/`--ymmetry` flag is a confirmed no-op in 6.2.0 (aliasing bug in upstream `CLI.java`); the counting net (item 2 below) must set `symmetryBreaking=0` via the `A4Options` Java API directly (see reference doc §"Solver options"), not via the `exec` CLI flag.
2. **Only verdict and model-count are canonical; instances are never compared.**
   - **Verdict (SAT/UNSAT)** is solver-independent and canonical.
   - **Model count** is canonical *only if symmetry breaking is identical on both sides.* Therefore the counting net runs the jar with **`symmetryBreaking = 0`** (raw satisfying assignments, no isomorph quotient), which is canonical and also matches mettle's early core (which has no symmetry breaking). A second, stricter count comparison at the default symmetry-breaking level is added later as an SBP-conformance net.
   - **Instances (the actual tuples)** depend on symmetry-breaking predicates, variable ordering, and the solver; two valid runs legitimately differ. We never diff instances against the jar. Instance *validity* is checked by our own evaluator (self-check net), not by the jar.
3. **`expect 0` / `expect 1` command annotations are mined as a zeroth oracle (Net 0)** — many corpus models encode their own expected verdict, giving a free cross-check that also validates our jar-runner itself.
4. **Determinism is scoped to self-consistency for a fixed solver build** — byte-identical output and enumeration order across runs/machines. This is explicitly **not** matching the jar's CNF or enumeration order (impossible and not attempted). The jar is matched only on verdict and (SB-off) count.
5. **Test infrastructure runs a JVM on purpose.** The *product* has no JVM; the *conformance harness / CI* drives the reference jar to regenerate the scorecard. This is stated plainly (not hidden) as part of the trust story. The scorecard is made third-party-reproducible by pinning the jar SHA and every corpus commit.

## Consequences
- The counting net (plan §4.3 Net 3) is usable from the first solving rung, not deferred, because SB-off counts are canonical and match the no-SB core.
- A reviewer/agent must never write a test that diffs instance tuples against the jar.
- CI depends on a JDK; releases of the product do not.

## Alternatives considered
Comparing instances directly (rejected: not canonical). Matching the jar's default symmetry breaking from day one (rejected: requires bit-exact SBP replication, deferred to a later dedicated net).
