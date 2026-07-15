# ADR-0006 — Licensing posture (mettle code, stdlib, corpora, oracle)

**Status:** Accepted
**Date:** 2026-07-15
**Bead:** mt-008 (decision by the product owner; facts gathered in
[reference/corpora.md](../reference/corpora.md) and
[reference/alloy6-reference.md §2](../reference/alloy6-reference.md))

## Context
Four distinct license questions were tangled in mt-008: (1) mettle's own
code, (2) the Alloy standard library (`util/*.als`) that a drop-in
replacement must bundle, (3) the conformance corpora, (4) the reference
jar. Upstream Alloy's own license is unsettled (repo `LICENSE` says
"NOT VALID YET! CURRENTLY CODE IS UNDER MIT LICENSE" mid-transition to
Apache-2.0; `util/*.als` carry no headers at all), and the portus-63
corpus aggregates GPL-3.0 and no-license sources.

## Decision (product owner, 2026-07-15)

1. **mettle's own code is licensed MPL-2.0.** File-level weak copyleft:
   distributed modifications to mettle's files must stay open; combining/
   linking into larger (including proprietary) works is expressly permitted.
   Applied via the root `LICENSE` (canonical MPL-2.0 text) and
   `license = "MPL-2.0"` in the workspace manifest, inherited by every
   crate. **No per-file Exhibit A headers**: MPL-2.0 Exhibit A explicitly
   allows the notice to live "in a location (such as a LICENSE file in a
   relevant directory) where a recipient would be likely to look" — the
   root `LICENSE` + per-crate `license` metadata is that location. Anyone
   extracting individual files for reuse elsewhere should carry the notice
   along.

2. **The Alloy stdlib is a clean-room rewrite, not vendored.** mettle
   ships its own `util/*.als` (and any other bundled models), written
   from the *documented module interfaces* (names/signatures must match —
   interfaces are not copyrightable) plus behavior pinned in the
   SEMANTICS_LEDGER and the conformance suite. Authors of these files
   must not copy from or work with upstream's `util/*.als` text open
   (note: copies exist locally under `corpus/alloytools-models/models/util/`
   — those are conformance *test inputs*, off-limits as source material
   for our stdlib). Much of `util/ordering`'s real behavior is analyzer
   special-casing (exact bounds, symmetry), which we reimplement
   regardless of whose text ships. Our rewrites are MPL-2.0 like the rest
   of the code. Tracked as bead mt-015 (Rung 2, with `open` resolution).

3. **Corpora are local-only, permanently.** `corpus/` stays git-ignored
   and is never redistributed: portus-63 aggregates 2× GPL-3.0 and 6×
   no-license sources (all-rights-reserved by default) and cannot be
   redistributed; the blanket local-only rule is simpler and safer than
   per-corpus carve-outs (Alloy4Fun's CC-BY-4.0 would permit it, but there
   is no need). Reproducibility comes from the committed provenance
   manifest ([reference/corpora.md](../reference/corpora.md)) and the
   fetch script (bead mt-009, `scripts/fetch-corpora.sh`).

4. **The reference jar stays git-ignored** (`oracle/`), re-downloaded by
   SHA per ADR-0002. Test infrastructure only; never shipped.

5. **NOTICE/attribution:** mettle currently retains no third-party text,
   so no NOTICE file is required. If that ever changes (a dependency's
   license demands it, or any third-party text is shipped), attribution
   obligations are handled in that PR and this ADR is superseded.

## Consequences
- `PORTING_RULES.md` "Legal hygiene" is updated by this ADR (its process
  requires an ADR for rubric changes — this is it): the "vendor
  `util/*.als` verbatim with headers intact" bullet is replaced by the
  clean-room rule, and the "Alloy is Apache-2.0" assumption is corrected
  to "unsettled upstream; study behavior, never copy text."
- The clean-room constraint makes the stdlib slightly more work (mt-015)
  but removes the last dependency on upstream's licensing mess from the
  shipped product entirely: a mettle release contains only MPL-2.0 code.
- Contributors' modifications to mettle files are guaranteed to remain
  open when distributed; embedding the `als-*` crates in other tools
  (open or closed) remains allowed.

## Alternatives considered
- **Apache-2.0 / MIT OR Apache-2.0** for mettle's code — maximally
  frictionless, but the owner values remixes staying open; MPL-2.0's
  file-level copyleft buys that at negligible adoption cost for an
  application-shaped project.
- **Vendoring upstream `util/*.als` verbatim + NOTICE** under the
  defensible MIT reading — lower effort, but keeps a permanent legal
  ambiguity inside the shipped artifact; rejected in favor of clean-room.
- **Committing redistributable corpora (Alloy4Fun, CC-BY-4.0)** —
  possible but unnecessary; a single local-only rule for all of
  `corpus/` is simpler.
