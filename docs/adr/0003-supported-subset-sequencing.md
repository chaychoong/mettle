# ADR-0003 — Supported-subset sequencing

**Status:** Accepted
**Date:** 2026-07-15

## Context
The North Star is "handles real models, exactly." Real models pervasively use cardinality (`#`), integers, and `util/ordering`. The original phase plan deferred integers and symmetry breaking to Phase 4 and treated `util/ordering` as a Phase-4 optimization. Some of that deferral collides with correctness on real models.

## Decision
1. **Cardinality (`#`) and integer-overflow semantics are handled from the first solving rung (Rung 3 / Phase 3), not deferred.** `#` is `Int`-typed and ubiquitous; Alloy's default **`forbid overflow = yes`** makes an overflowing arithmetic/cardinality expression vacuously exclude the instance, which changes the *verdict*, not just the instance. A "no-integers" Phase 3 that still supports `#` would silently disagree with the jar. So: implement `#` with a fixed sufficient bitwidth and replicate the default overflow-forbid rule from the start; the overflow rule gets a top-priority Semantics Ledger entry now. The *cursed* integer surface that can still wait is general arithmetic (`plus`/`minus`/`sum`), not the overflow rule itself.
2. **`util/ordering` is treated as semantics, not merely an optimization.** Opening `util/ordering[S]` *induces* `first`/`next`/`last` as a total order pinned to atom order and constrains bounds — it changes counts and verdicts. Its **semantics** are required whenever a model opens it (early). Only the **symmetry-breaking exploitation** of ordering (Kodkod's special-case) is a later performance item.
3. **The fuzzer is split.** A **mutation fuzzer over the existing corpus** (cheap, needs no type-system knowledge; great for parser/type robustness) lands at Rung 1. A **generative well-typed-model fuzzer** (near-as-hard as the type checker it tests; partly circular) is deferred to Rung 4+.

## Consequences
- Rung 3's "first solve" is demoed on *real* models (with cardinality), not toys — better for the product owner's sense of progress. An internal toy-only solve may happen first but is not a human-facing gate.
- Integer/overflow semantics enter the Semantics Ledger in Phase 3.

## Alternatives considered
Excluding `#` from Phase 3 (rejected: cardinality is in a huge fraction of real models; the first solve would feel broken).
