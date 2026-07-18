# ADR-0012 — Rung-4 architecture: integers, strings, seq, counting & symmetry

**Status:** Proposed · **Date:** 2026-07-18 · **Beads:** mt-043 (this ADR + the
pinned contract), mt-044–mt-048 (implementation), mt-050 (exit gauge)

## Context

Rung 4 is "it agrees with Alloy across everything I have" (ROADMAP): the
solve-gauge reaches **0 verdict disagreements** with only temporal (Rung 6),
the jar's own errors, and an honest small capacity remainder left as typed
defers, and the SB-0 counting net loses its `skip_fo_skolem` family. The
Rung-3 exit left the coverage picture (mt-037 gauge over 564 corpus commands):
`lower:lowering` 217 (≈140 resolver-recording gaps → mt-040, 39 integer-ordering
builtins, remainder seq/arithmetic), `capacity`/`over_budget`/`encode` 122 (perf
→ mt-049), `temporal` 22 (Rung 6), `scope` 10 (String), `higher_order` 4 (jar
errors, at parity); counting `skip_fo_skolem` 55, `skip_mettle_cap` 23,
`COUNT_MISMATCH` 3 (mt-041).

The behavior the Rung-4 beads implement is now pinned in
[reference/alloy6-translation.md](../reference/alloy6-translation.md) §11–§16
(mt-043) against the jar at commit `794226dd`, with the four Ledger corners
drafted (LEDGER-005 integers *proposed*, LEDGER-006 cardinality / LEDGER-007
String / LEDGER-008 seq *verified*). This ADR pins the **Rust structure** for
that behavior — semantics faithful, structure idiomatic (PORTING prime
directive) — extending the ADR-0005 shapes and the Rung-3 machinery (ADR-0011),
not redesigning them. It also records the two owner-visible decisions of the
rung: the **symmetry-breaking posture** and the **Rung-4 exit gate**.

## Decision

### 1. Integer arithmetic extends the existing two's-complement encode layer — with the evaluator matched-pair rule as a binding invariant.

mt-033 already encodes the Rung-3 integer slice (`Const`, `#` cardinality,
`int[·]`) as two's-complement bit-vectors honoring the LEDGER-001 overflow
switch, and mt-034's evaluator mirrors it exactly. mt-044 adds `plus`/`minus`/
`mul`/`div`/`rem`, the three shifts, unary negate, `sum x|ie`, and integer
if-then-else as new `IntExprKind` variants over the **same** encode layer
(translation-ref §11.1), with the per-op two's-complement semantics of §11.2
(div toward zero, rem sign-of-dividend, `<<`/`>>`/`>>>` = logical-left/
arithmetic-right/logical-right) and the forbid-mode **Milicevic/Jackson polarity
guard** of §11.3 threaded on the existing `Pol` seam (mt-038).

**Binding invariant (mt-034's differential keeps its teeth):** every new integer
op is added to **both** the encoder and the evaluator, and the encoder↔evaluator
differential (brute-force accept-count = solver SB-0 count) is extended to cover
it, so the two implementations stay a **matched pair**. A new op that lands in
only one is a review-blocking defect. This is what makes "self-verified" hold as
the integer surface grows — it is not optional.

### 2. The `Int/min|max|next|zero` builtin relations are allocated in the bounds builder.

`Int/next` (binary, consecutive-int chain) and `Int/zero` (`{0}`) are allocated
as exact constant relations in `bounds_builder` (translation-ref §12), because
`util/integer`'s `next`/`prev`/`nexts`/`prevs` and the seq contiguity fact
(§14) reference them. `Int/min`/`Int/max` may be lowered as **integer constants**
(`min`/`max` of the bitwidth), matching the jar's own translation
(`visit(ExprConstant)` maps `MIN`/`MAX` to `IntConstant`, not the relations) —
so mettle need not allocate `Int/min`/`Int/max` relations at all. This unlocks
the 39 integer-ordering-builtin `lower:lowering` defers (mt-044).

### 3. String atoms are minted in scope/universe computation, not in bounds or lowering.

Per translation-ref §13 (LEDGER-007), `als_core::scope` collects the referenced
string literals (command formula + all reachable facts incl. top-level + field
decls, recursing into called funcs), pads with `"String%d"` atoms to an exact
`String` scope, expands the scope to `max(N, #referenced)`, and appends them
**last** in the universe; the `String` relation is bound exactly to them, each
literal getting its private singleton relation for `= "lit"`. mettle orders the
atoms **deterministically** (the jar's `HashSet` order is nondeterministic and
need not be matched — string atoms are symmetric, so verdict and SB-0 count are
order-invariant). This replaces the mt-037 typed defer for non-zero String
scopes (mt-045) and un-defers String literals in goals. **Correction carried
into the contract:** the padding atoms are `"String%d"`, not `unused%d` (which is
the jar's *instance-display* name for sig-unclaimed atoms) — a documented
discrepancy in LIMITATIONS/STATE that mt-045 must not reproduce.

### 4. The `seq` desugar splits across bounds and lowering, mirroring the §2.5 field-fact split.

`seq/Int`'s exact bound already lives in the bounds builder (mt-030). mt-046 adds:
the `seq X` field desugar to `seq/Int -> lone X` (an arrow value constraint the
lowerer already handles via `arrow_value_constraint`, mt-038), and the single
implicit **contiguity fact** `dom(f) − dom(f).(Int/next) ⊆ Int/zero` synthesized
at **lowering** (field-fact assembly, §2.5) using the §12 builtin relations —
consistent with the pinned split "mt-030 owns sig/scope constraints, the lowerer
owns field facts". `util/sequniv`/`util/seqrel` functions lower as ordinary
funcs; their clean-room rank-arithmetic bodies get a differential check when
mt-046 exercises them (the clean-room-stdlib Ledger corner).

### 5. First-order skolemization extends mt-038's higher-order skolem machinery.

mt-038 already skolemizes higher-order decls at effective-existential,
universal-free positions into free relations, threading a `SkolemPolarity`. mt-047
extends the **same** machinery to top-level **first-order** existentials
(translation-ref §15): a `some` at positive polarity or an `all` under a `check`'s
negation, not nested under any universal (the depth-0 gate), becomes a free
constant relation named **`$<cmdLabel>_<var>`** (or `$<var>` for a `$`-bearing
label), lower `{}`, upper = the decl bound's `abstract_upper`, with the decl's
membership conjoined and the var bound to it. Instances then *show* the skolem
witness (drop-in display), and enumerating its assignments makes the
`skip_fo_skolem` counting family (55 commands) exact — e.g. `run { some x: A |
x=x } for 3` becomes SB-0 count 12, matching the jar (§15). First-order
quantifiers under a universal stay direct (depth 0 does not skolemize them);
ADR-0011's "no FO skolemization in Rung 3" is thereby superseded **for Rung 4**.

### 6. Symmetry-breaking posture: SB-0 stays the counting yardstick; lex-leader is an added perf + parity net.

Per translation-ref §16: the jar's default `symmetryBreaking = 20` is a **bound on
the lex-leader predicate length**; it changes the enumerated count and performance
but **never the verdict** (a symmetry-reducing constraint removes only isomorphic
satisfying assignments). ADR-0002's **SB-0 remains the canonical counting net**
(the only solver-independent count, and the regime mettle's no-SB core already
is). mt-048 ports the Kodkod lex-leader predicate as a **performance feature plus a
dedicated default-symmetry (SB=20) verdict/count net** — off the verdict gate,
never touching the SB-0 counting net, requiring bit-exact lex-leader replication
only for the SB=20 comparison. The `expect 1 ⇒ symmetry 0` coupling (probe T3)
stays honored by the harness.

### 7. The Rung-4 exit gate (awaits owner blessing).

As proposed in the TASKS.md Rung-4 header: **solve-gauge 0 verdict disagreements
with every defer bucket accounted for** — the only remaining typed defers are
temporal (Rung 6), the jar's own errors (higher-order parity, already holding),
and an honest small capacity/budget remainder; the **counting net loses its
`skip_fo_skolem` family** (mt-047) and the **mt-041 count mismatches**. Scorecard
motion: baseline overlap climbs from 187/392 agree toward "everything
non-temporal agrees." Per mt-027's standing rule, any bead touching type
machinery notes its effect on the 314 alloy4fun over-accepts. **This gate is the
one genuine owner decision of the ADR; silence = the proposal stands** (per the
operating contract's "surface genuine decisions before dependent work").

## Consequences

- Implementation beads land per the TASKS.md sequencing: mt-040 (recording gaps,
  interleaves freely — biggest unlock, no contract dependency), then
  mt-044→045→046 (shared encoder/evaluator surface, integers first), mt-047/048
  behind this contract, mt-049 opportunistic, mt-050 the exit gauge.
- `als_core`'s encode/eval layers grow the arithmetic ops as a matched pair;
  `bounds_builder` grows `Int/next`/`Int/zero`; `scope` grows String minting;
  `lower` grows the seq contiguity fact and FO skolemization. No new crate, no
  Java structure ported (closed enums + exhaustive match, PORTING R1).
- LEDGER-005 must reach `verified` (its two named residuals probed shut) and be
  owner-`approved` before mt-044's arithmetic ships; LEDGER-006/007/008 are
  `verified` and await owner approval. LEDGER-001's conformance test lands at
  mt-044.
- The SB-20 net (mt-048) is additive; ADR-0002's counting config is unchanged.
- FO skolemization changes decoded instances (they gain `$cmd_var` relations) and
  SB-0 counts (they rise to the jar's) — a deliberate, verdict-neutral change that
  supersedes ADR-0011 decision on FO skolemization for Rung 4 only.

## Alternatives considered

- **Flat `goal ∧ ¬overflow` for forbid mode** — rejected: wrong. The jar's forbid
  semantics are polarity- and quantifier-sensitive (§11.3); a flat conjunction
  flips the universal-position case (probe I11: forbid is SAT, a flat `¬overflow`
  would give UNSAT). mettle must thread polarity through the overflow guard.
- **Allocate `Int/min`/`Int/max` as relations** — rejected as unnecessary: the jar
  translates `min`/`max` to int constants, so relations would be dead weight;
  allocate only `Int/next`/`Int/zero`, which are actually referenced.
- **Match the jar's String atom order** — rejected: it is `HashSet` iteration
  order (nondeterministic, probe S2), un-reproducible and pointless (string atoms
  are symmetric). mettle picks a deterministic order; verdict/SB-0 count are
  order-invariant (STYLE D1 = self-consistency, not jar-matching).
- **Skip FO skolemization (keep ADR-0011's Rung-3 stance)** — rejected for Rung 4:
  it is the only way to make the `skip_fo_skolem` counting family exact and to show
  skolem witnesses in instances (drop-in display); the machinery already exists
  (mt-038), so the cost is extending a seam, not new architecture.
- **Implement SB=20 as the default counting regime** — rejected: SB-0 is the only
  solver-independent count (ADR-0002); SB=20 counts depend on bit-exact lex-leader
  replication and are a dedicated parity net, not the yardstick.
- **A separate temporal/string mega-solver** — out of scope: temporal is Rung 6;
  String is a small universe-computation addition, not a new solving mode.

Related: [ADR-0002](0002-conformance-oracle.md) (verdict + SB-0 count gauge),
[ADR-0011](0011-rung3-translation-solving-architecture.md) (the Rung-3 machinery
this extends; FO-skolemization stance superseded for Rung 4),
[ADR-0005](0005-core-ir-type-skeleton.md) (IR/bounds/CNF shapes),
[ADR-0006](0006-licensing-posture.md) (clean-room stdlib — the seq/String stdlib
bodies stay clean-room), [reference/alloy6-translation.md](../reference/alloy6-translation.md)
§11–§16 (the pinned behavior), SEMANTICS_LEDGER LEDGER-001 (overflow switch),
LEDGER-005/006/007/008 (the corners this implements against).
