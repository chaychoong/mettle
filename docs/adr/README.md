# Architecture Decision Records

Each ADR captures one non-trivial decision, its context, and its consequences. ADRs are immutable once **Accepted**; to change a decision, add a new ADR that supersedes the old one (and flip the old one's status to `Superseded by ADR-XXXX`). Nothing is deleted.

**Status values:** `Proposed` · `Accepted` · `Superseded by ADR-XXXX`

| ADR | Title | Status |
|-----|-------|--------|
| [0001](0001-name-mettle.md) | Project name: **mettle** | Accepted |
| [0002](0002-conformance-oracle.md) | Conformance oracle & yardstick | Accepted |
| [0003](0003-supported-subset-sequencing.md) | Supported-subset sequencing (cardinality, overflow, ordering, fuzzer) | Accepted |
| [0004](0004-docs-and-task-system.md) | Documentation & task-tracking system | Accepted |

Template for new ADRs: **Context → Decision → Consequences → Alternatives considered**, with `Status:` and `Date:` headers, and a `Supersedes` / `Superseded by` line when relevant.
