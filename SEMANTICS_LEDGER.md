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
- `verified` = confirmed empirically against the pinned jar, **with no open residual uncertainties** — every soft spot the drafting work flagged has been probed shut (or has amended the rule).
- `approved` = product owner has blessed it as canonical. **Only `approved` rules are safe to implement against.**
- Process rule (owner, 2026-07-16): an entry is put to the owner for approval **only at `verified`** — never with "re-derive later" caveats attached. If stating the rule wrong is a risk, the answer is more probes, not a caveated sign-off.

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

### LEDGER-004 — `util/ordering` exact bounds & order pinning
**Rule:** Opening `util/ordering[S]` always forces sig `S`'s **total** population to be **exact** at whatever scope `S` resolves to — independent of the `exactly` keyword, of `S`'s multiplicity qualifier, and of whether `first`/`next`/`last`/`prev` are ever referenced. **(a)** When `S` has no proper subsig, or its subsigs leave no partition choice, the order's `first`/`last`/`next` are *additionally* bound to exact constants over `S`'s atoms in universe order (`first = S$0`, `last = S$<n-1>`, `next` = the consecutive-atom successor) — the linear order is fully pinned, independent of the symmetry-breaking setting. **(b)** When `S` has a proper subsig with non-exact scope, or two-or-more subsigs (even if individually exact), the constant binding does **not** engage: `first`/`next`/`last` are governed only by the ordinary `pred/totalOrder` constraint, and genuine order freedom (which chain rank carries which subsig tag) survives as multiple distinct instances at every symmetry setting.
**Status:** `verified` (2026-07-16 — the exhaustive T10–T19 matrix closed every §9 residual and **amended the rule**: the original statement was correct for childless sigs but missed the subsig-conditional half; the drafted-then-amended history is preserved below). **Awaiting owner `approved`; gates bead mt-035.**
**Evidence:** probes T4/T4b plus the mt-028 exhaustive matrix T10-T19 in [reference/alloy6-translation.md](docs/reference/alloy6-translation.md) §5/§10.1 (jar-verified 2026-07-16, OpenJDK 21, `oracle/org.alloytools.alloy.dist.jar` 6.2.0). Confirms: instance count = 1 at both symmetry 20 and symmetry 0 for a childless ordered sig at every tested size 2-6 (T10a-e), `next` always the plain consecutive chain `S$0->S$1->...->S$<n-1>` (resolves the old ">3-atom orders" residual); two independent ordered sigs pin independently (T12); an enum auto-opens ordering with the same pinning, `first` = the first **declared** constant (T13); the pinning is triggered purely by the `open` even when `first`/`next`/`last` are never referenced in the command (T19); a conflicting fact on `first` is UNSAT, proving the binding is a genuine constant not a solver preference (T16); a `var` ordered sig is rejected at parse/resolve with an explicit message (T18).
**IMPORTANT — the matrix also found a genuine counterexample to the rule as stated** (T14a-e, T15; resolves the old "partially scoped ordered sigs" residual, §9): when the ordered sig `S` has a proper subsig with **non-exact** scope, or **two-or-more** subsigs (even if each is individually `exactly`-scoped), the exact-constant shrink on `first`/`next`/`last` does **not** engage — `pred/totalOrder` is instead solved as an ordinary constraint, and genuine order freedom (which chain rank carries which subsig tag) survives as multiple distinct SAT instances at **both** symmetry 20 and symmetry 0 (e.g. T14b: 3 instances at sym20, 6 at sym0, all sharing the identical atom-name population `{A$0,A$1,B$0}` but with `B$0` at a different chain rank in each). The sig's **overall exact-scope forcing** (part (a) of the rule) is unaffected and holds unconditionally in every subsig configuration tested; only the **exact-constant** binding of first/next/last (part (b)) is subsig-conditional. An unrelated field reference to `S` (not a subsig) does not trigger this — T15 is a clean isolating control.
**Rule history:** the original mt-028 draft stated only the childless-sig behavior ("forces exact scope + binds first/last/next to exact constants, unconditionally"); the T14/T15 probes showed the constant-binding half is subsig-conditional, and the rule above is the amended statement (2026-07-16).
**Test:** _(added with the Rung-3 ordering work, mt-035 — must cover both the plain-sig exact-shrink path AND the subsig fallback path as two distinct behaviors, not one)_

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
