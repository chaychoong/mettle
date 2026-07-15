# ADR-0003 — Supported-subset sequencing

**Status:** Accepted
**Date:** 2026-07-15

## Context
The North Star is "handles real models, exactly." Real models pervasively use cardinality (`#`), integers, and `util/ordering`. The original phase plan deferred integers and symmetry breaking to Phase 4 and treated `util/ordering` as a Phase-4 optimization. Some of that deferral collides with correctness on real models.

## Decision
1. **Cardinality (`#`) and integer-overflow semantics are handled from the first solving rung (Rung 3 / Phase 3), not deferred.** `#` is `Int`-typed and ubiquitous, and overflow behavior is *verdict-affecting*: whether an overflowing arithmetic/cardinality term wraps (silent two's-complement) or excludes the instance changes SAT/UNSAT. A "no-integers" Phase 3 that still supports `#` would silently disagree with the oracle. So `#` is implemented with a fixed sufficient bitwidth (default 4, range −8..7) and the overflow rule is pinned from the start; general arithmetic (`plus`/`minus`/`sum`) beyond the overflow rule can still wait.

   **Correction (2026-07-15, empirical — see [reference/alloy6-reference.md](../reference/alloy6-reference.md) §3(c)):** an earlier draft of this ADR asserted Alloy's default is *forbid overflow*. That holds only for the **GUI** ("Prevent overflows" ships checked). The **headless jar / `A4Options` API** — which is our oracle — defaults to **allow overflow** (`noOverflow=false`, silent wraparound), independently reproduced (`run { plus[7,7] < 0 } for 4 int` → SAT by default, UNSAT under `-n`). Because the default **differs by entry point**, mettle must choose its canonical overflow behavior *explicitly* rather than inherit a default, and the conformance harness must set the oracle's `noOverflow` to match mettle's choice so both sides compare like-for-like. The canonical choice is a human-owned Semantics Ledger decision ([LEDGER-001](../../SEMANTICS_LEDGER.md)), **decided 2026-07-15: match the GUI default — forbid overflow**, since a drop-in replacement should reproduce the Alloy that users actually run. A `--[no-]overflow` flag toggles it.
2. **`util/ordering` is treated as semantics, not merely an optimization.** Opening `util/ordering[S]` *induces* `first`/`next`/`last` as a total order pinned to atom order and constrains bounds — it changes counts and verdicts. Its **semantics** are required whenever a model opens it (early). Only the **symmetry-breaking exploitation** of ordering (Kodkod's special-case) is a later performance item.
3. **The fuzzer is split.** A **mutation fuzzer over the existing corpus** (cheap, needs no type-system knowledge; great for parser/type robustness) lands at Rung 1. A **generative well-typed-model fuzzer** (near-as-hard as the type checker it tests; partly circular) is deferred to Rung 4+.

## Consequences
- Rung 3's "first solve" is demoed on *real* models (with cardinality), not toys — better for the product owner's sense of progress. An internal toy-only solve may happen first but is not a human-facing gate.
- Integer/overflow semantics enter the Semantics Ledger in Phase 3.

## Alternatives considered
Excluding `#` from Phase 3 (rejected: cardinality is in a huge fraction of real models; the first solve would feel broken).
