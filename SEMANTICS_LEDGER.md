# Semantics Ledger

**Status:** living document · **Owner: human (product owner).** Agents implement *from* this ledger; they do not author settled rules into it.

## Purpose
For every corner where the reference Alloy jar's behavior *is* the spec, this ledger records a **one-sentence behavioral rule** plus a link to the conformance test that pins it. This is the understanding the project exists to produce. The rule is: read the reference until the behavior can be stated in one sentence, verify it empirically against the pinned jar, write it here with a test, then implement idiomatically.

## Entry format
```
### LEDGER-NNN — <corner>
Rule: <one sentence, testable>.
Status: proposed | verified | approved
Evidence: <how it was checked against the pinned jar>
Test: <path to the conformance test>
```
- `proposed` = drafted by an agent/tech lead, **not yet human-approved**.
- `verified` = confirmed empirically against the pinned jar.
- `approved` = product owner has blessed it as canonical. **Only `approved` rules are safe to implement against.**

---

## Entries

### LEDGER-001 — integer overflow default ("forbid overflows" / `noOverflow`)
**Rule:** mettle treats integer/cardinality arithmetic exceeding the bitwidth as **forbidden by default** — an overflowing term excludes the instance (matching the Alloy GUI's default "Prevent overflows" = on). A `--[no-]overflow` flag switches to allow/wraparound semantics.
**Status:** `approved` (product owner, 2026-07-15). Facts below `verified`; safe to implement against.
**Evidence:** Alloy 6.2.0's default is **entry-point-dependent** (verified 2026-07-15, see [reference/alloy6-reference.md](docs/reference/alloy6-reference.md) §3(c) — reproduced by tech lead): GUI default = forbid (`noOverflow=true`); headless jar / `A4Options` default = allow/wraparound (`noOverflow=false`). Decisive test: `run { plus[7,7] < 0 } for 4 int` → **SAT** (allow) by default, **UNSAT** under `-n` (forbid). Default bitwidth = 4 (range −8..7).
**Decision (approved 2026-07-15):** canonical default = **forbid overflow**, to match the Alloy GUI's default experience (the Alloy users actually run). The conformance harness sets the oracle's `noOverflow` to match mettle's active setting so the scorecard always compares like-for-like.
**Test:** _(added with the Rung-3 integer work)_

---

## Corners that NEED entries (tracked; not yet written)
These are known to be behavior-defining and version-sensitive. Each becomes a numbered, verified, approved entry before the code that depends on it ships.

- **Integer overflow** — drafted as [LEDGER-001](#ledger-001--integer-overflow-default-forbid-overflows--nooverflow) above; awaiting owner approval of the canonical default.
- **Integer wraparound & bitwidth** — two's-complement semantics, default bitwidth, `Int` sig.
- **`util/ordering`** — the relations/bounds it induces (`first`/`next`/`last`, total order pinned to atom order).
- **Cardinality `#`** — typing, coercion to `Int`, interaction with overflow.
- **Overloading resolution** — same field name across disjoint sigs.
- **`seq` semantics** — `util/sequniv`, `seq` fields.
- **Type/relevance checking** — which expressions warn vs error vs pass (Edwards/Jackson/Torlak).
- **Iteration-order-sensitive numbering** — anywhere the jar's behavior depends on declaration/atom order.

> No rule above is settled yet. Do not implement against this file until an entry exists and is marked `approved`.
