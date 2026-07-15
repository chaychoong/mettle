# ADR-0001 — Project name: mettle

**Status:** Accepted
**Date:** 2026-07-15

## Context
The project needs a name before Phase 1 (renames after publication are expensive). Candidates in the Alloy/metallurgy space were mostly taken on crates.io: `alloy`/`alloy-rs` (squatted by the Ethereum stack), `forge`/`crucible`/`smelt`/`ingot`/`anneal`/`kiln`/`assay`/`temper`/`quench` all taken. `sterling` is both taken and the name of the Alloy visualizer we integrate, so it was never a candidate.

## Decision
The project is named **mettle**.
- Rationale: `mettle` is a homophone of *metal* (the alloy domain), it means *tested resilience* ("prove your mettle") — exactly what a model checker does to a spec — and Rust is the oxidation of that same metal. The name is the pitch.
- **Published crate / binary / install name:** `mettle` (`cargo install mettle`, `brew install mettle`, CLI `mettle check foo.als`). Verified free on crates.io.
- **Library crates keep the `als-*` prefix** (`als-syntax`, `als-types`, `als-core`, `als-solve`, `als-instance`, `als-sterling`, `als-cli`, `als-conform`).
- **GitHub home:** `github.com/mettle-lang/mettle` — the bare `github.com/mettle` handle is taken by an unrelated company; `-lang` reads as "a language project," which fits the positioning.

## Consequences
- `mettle` is the user-facing identity; `als-*` is the internal crate namespace. Both must stay consistent across docs and code.
- No Alloy/formal-methods project currently uses the name (checked), so there is no domain collision.

## Alternatives considered
`hallmark` (assay-office certification stamp — perfect metallurgy meaning, but unavoidable greeting-card brand shadow); `proofmark`, `eutectic` (distinctive but opaque). All viable; `mettle` won on the metal-homophone + tested-resilience double meaning.
