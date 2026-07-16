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

### LEDGER-002 — resolve/typecheck verdict boundary (warnings never fatal) + warning parity
**Rule:** mettle's `check` verdict is binary — ACCEPT iff the reference's `resolveAll` returns, REJECT iff it throws — and **warnings never change the default verdict** (matching the jar). **Additionally (owner requirement): mettle must catch the same issues the jar warns about** — wherever the jar emits a warning, mettle emits a corresponding warning (equivalent issue and position; wording may differ).
**Status:** `approved` (product owner, 2026-07-16). Verdict facts `verified`. **Parity measured (mt-023, 2026-07-16):** all 20 warning classes implemented; corpus 0 missing; alloy4fun 99.80% files identical, 192 warnings missing (0.19% of files) + 20 extra, both remainders root-caused in [reference/warning-parity.md](docs/reference/warning-parity.md). `mettle check --strict` shipped.
**Evidence:** Reference sources at commit `794226dd` (warnings emitted only after full success; `A4Reporter.NOP` drops them) + mt-016 probes 01/40/42 + the mt-020 differential over 150,891 alloy4fun codes ([reference/alloy4fun-resolve-pass.md](docs/reference/alloy4fun-resolve-pass.md)). See [reference/alloy6-resolution.md](docs/reference/alloy6-resolution.md) §0/§5.2/§5.3. Current gap: mettle emits only part of the §5.2 catalog (see [LIMITATIONS.md](LIMITATIONS.md)); the relevance/redundancy classes need the precise relevant-type pass (bead mt-022).
**Test:** `crates/als-types/tests/resolve_probes.rs` (warning cases assert ACCEPT); the `resolve_gauge` differential harness (mt-023 extends it to compare warning sets).

### LEDGER-003 — overload/ambiguity resolution posture (accept-lean interim)
**Rule:** mettle resolves overloaded names/calls by the reference's candidate ladder where its types are precise enough, and where they are not it **accepts with the first minimum-weight candidate rather than rejecting** — mettle must never reject a model the jar accepts, at the measured cost of ~4.2% over-acceptance on jar-rejected models.
**Status:** `approved` (product owner, 2026-07-16 — "as long as we have a plan to close the similarity gap": the plan is bead **mt-022** (precise relevant-type propagation), which re-enables the reverted tightenings and re-runs the gauge; this entry is then re-proposed with the new numbers). Measurements `verified` by the mt-020 gauge: 0 drop-in violations, 6,300 over-accepts, tightening measured-and-reverted per [ADR-0009](docs/adr/0009-fused-resolve-pass-accept-lean.md).
**Evidence:** [reference/alloy4fun-resolve-pass.md](docs/reference/alloy4fun-resolve-pass.md); divergence classes + frequencies in [LIMITATIONS.md](LIMITATIONS.md). Supersession path: backlog bead mt-022 (precise types) re-runs the gauge and re-proposes this rule.
**Test:** `crates/als-types/tests/resolve_probes.rs` (probe 15 call-form reject; `_mt020` regression tests); the `resolve_gauge` harness.

---

## Corners that NEED entries (tracked; not yet written)
These are known to be behavior-defining and version-sensitive. Each becomes a numbered, verified, approved entry before the code that depends on it ships.

- **Integer overflow** — done: [LEDGER-001](#ledger-001--integer-overflow-default-forbid-overflows--nooverflow) above, `approved` 2026-07-15 (canonical default = forbid).
- **Integer wraparound & bitwidth** — two's-complement semantics, default bitwidth, `Int` sig.
- **`util/ordering`** — the relations/bounds it induces (`first`/`next`/`last`, total order pinned to atom order) and the analyzer's exact-bounds + symmetry special-casing for the `exactly`-marked param (resolve-level structure pinned in [reference/alloy6-resolution.md](docs/reference/alloy6-resolution.md) §7.1; solve-level behavior needs its entry at Rung 3).
- **Clean-room stdlib body semantics** — the mt-015 judgment calls that only solving can verify: `util/time` macro bodies, `util/relation` `complete`, rank arithmetic in `natural`/`sequence`/`seqrel` (flagged in the mt-015 report and [reference/alloy4fun-resolve-pass.md](docs/reference/alloy4fun-resolve-pass.md); each becomes an entry when Rung 3-4 differential runs exercise it).
- **Cardinality `#`** — typing, coercion to `Int`, interaction with overflow.
- **Overloading resolution** — resolve-level accept/reject pinned by [LEDGER-003](#ledger-003--overloadambiguity-resolution-posture-accept-lean-interim) (proposed); anything solve-visible (which candidate's *value* is used) still needs its own entry.
- **`seq` semantics** — `util/sequniv`, `seq` fields.
- **Type/relevance checking** — accept/reject boundary pinned by [LEDGER-002](#ledger-002--resolvetypecheck-verdict-boundary-warnings-never-fatal) (proposed); the per-warning firing conditions remain open (resolution-doc §9).
- **Iteration-order-sensitive numbering** — anywhere the jar's behavior depends on declaration/atom order.

> No rule above is settled yet. Do not implement against this file until an entry exists and is marked `approved`.
