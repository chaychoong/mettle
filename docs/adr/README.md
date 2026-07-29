# Architecture Decision Records

Each ADR captures one non-trivial decision, its context, and its consequences. ADRs are immutable once **Accepted**; to change a decision, add a new ADR that supersedes the old one (and flip the old one's status to `Superseded by ADR-XXXX`). Nothing is deleted.

**Status values:** `Proposed` · `Accepted` · `Superseded by ADR-XXXX`

| ADR | Title | Status |
|-----|-------|--------|
| [0001](0001-name-mettle.md) | Project name: **mettle** | Accepted |
| [0002](0002-conformance-oracle.md) | Conformance oracle & yardstick | Accepted |
| [0003](0003-supported-subset-sequencing.md) | Supported-subset sequencing (cardinality, overflow, ordering, fuzzer) | Accepted |
| [0004](0004-docs-and-task-system.md) | Documentation & task-tracking system | Accepted |
| [0005](0005-core-ir-type-skeleton.md) | Core IR type skeleton (arenas, AST, relational IR, CNF boundary) | Accepted |
| [0006](0006-licensing-posture.md) | Licensing posture: MPL-2.0 code, clean-room stdlib, local-only corpora | Accepted |
| [0007](0007-rung1-lexer-parser-architecture.md) | Rung-1 syntax front end: hand-written lexer + recursive-descent/Pratt parser | Accepted |
| [0008](0008-rung2-resolver-architecture.md) | Rung-2 resolver & type-checker architecture (`als-types`, two-pass, typed-ID world) | Accepted (dec. 4 amended by 0009) |
| [0009](0009-fused-resolve-pass-accept-lean.md) | Fused resolve pass + accept-lean interim posture (amends 0008; mt-020 decides tightening) | Accepted (scheduling superseded by 0010) |
| [0010](0010-hundred-percent-before-signoff.md) | Owner gate: ~100% resolve similarity before the Rung-2 touchpoint (mt-022/023 now) | Accepted (outcome recorded) |
| [0011](0011-rung3-translation-solving-architecture.md) | Rung-3 translation & solving architecture + the SAT-solver decision (hand-rolled CDCL; owner-approved) | Accepted (FO-skolemization stance superseded for Rung 4 by 0012) |
| [0012](0012-rung4-integers-strings-counting.md) | Rung-4 architecture: integers, strings, seq, FO skolemization, symmetry posture + the Rung-4 exit gate | Accepted — gate blessed 2026-07-25 (§7 records how), Rung 4 closed |
| [0013](0013-verification-instrument-never-trades-coverage.md) | The verification instrument never trades coverage for speed (owner-decided; the mt-057 fast lane built, measured at 6%, and deleted) | Accepted |
| [0014](0014-rung5-repl-slice-before-rung6.md) | A thin Rung-5 slice (evaluator REPL only) before Rung 6, then temporal, then the rest of Rung 5 | Accepted (owner-delegated call, 2026-07-25) |
| [0015](0015-rung6-temporal-architecture.md) | Rung-6 temporal architecture: bounded lasso solving as per-length unrolling on the existing CDCL; unbounded (electrod) out of scope | Accepted (owner-blessed at the combined review, 2026-07-28) |
| [0016](0016-rung5-remainder-serve-xml-packaging.md) | Rung-5 remainder: jar-exact instance-XML writer, `mettle serve` on Sterling's provider protocol, cargo-dist packaging | Proposed (both owner forks RESOLVED 2026-07-27: own browser-first frontend, nothing upstream embedded; crates.io skipped outright — blessing batched to the combined feature-complete review) |
| [0017](0017-gauge-default-budgets-paired-frontier.md) | Gauge default budgets on a measured paired-knob frontier; pairing rule standing (amended mt-082: conflicts → 25k after the ADR-0018 encoder reshape) | Accepted (tech-lead, zero-regression measured) |
| [0018](0018-encoder-structural-sharing.md) | Encoder structural sharing: value cache + support-bounded closure + widened memo (the family-C encode-cost fix) | Accepted (tech-lead, on the mt-080 profile) |
| [0019](0019-optional-cadical-backend.md) | Optional CaDiCaL SAT backend behind the `Solver` trait — instrument first, `--solver` surface second; own CDCL stays default + yardstick | Accepted (owner-decided, 2026-07-29) |

Template for new ADRs: **Context → Decision → Consequences → Alternatives considered**, with `Status:` and `Date:` headers, and a `Supersedes` / `Superseded by` line when relevant.
