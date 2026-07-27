# ADR-0016 — The Rung-5 remainder: instance XML, `mettle serve`/Sterling, packaging

**Status:** Proposed — both owner forks RESOLVED same day (see "Resolutions"
at the end: Decision 3 → option C browser-first own frontend; Decision 5 →
skip crates.io outright); formal blessing rides with the owner's new
batch-all-human-tests-at-feature-complete cadence
· **Date:** 2026-07-27 · **Beads:** mt-070 (this planning chunk), mt-071
(instance-XML writer), mt-072 (`mettle serve` provider backend), mt-075
(first-party frontend), mt-076 (temporal trace enumeration), mt-073
(release packaging), mt-074 (nix flake package output)

## Context

Rung 6 (temporal) is implementation-complete and its gate is with the owner
(ADR-0015). Per ADR-0014's standing sequence, the remaining Rung-5 pieces are
now due: **Sterling visualization** (`mettle serve`) and **one-command
install/packaging**, against ROADMAP Rung 5's bar — *"fresh install →
visualized instance in under a minute, no docs."* The evaluator REPL, the
first Rung-5 piece, shipped at mt-062.

mt-070 ran three recon/probe waves, all landed and tech-lead-verified:

- **The jar's instance-XML schema is now pinned** in
  [reference/alloy6-instance-xml.md](../reference/alloy6-instance-xml.md)
  (probe wave X-01..X-09b; the six load-bearing cells re-run by the tech
  lead, byte-identical). Two facts dominate the design: the real GUI/CLI
  path always passes every reachable user `fun`/`pred` as `macros`, which
  both mints `m<i>`-namespace skolems for zero-arg `fun`s and — when such a
  `fun` has nonzero past-depth — makes the physical `<instance>` block count
  `tracelength + extra·(tracelength − loopState)`, *not* `tracelength`; and
  sig/field IDs are lazy-memoized in touch order, not declaration order.
  Both are fully pinned and deterministic, so they are portable.
- **Sterling's integration contract is pinned** in
  [reference/sterling.md](../reference/sterling.md) — an *external-tool*
  contract, **not** jar authority: the reference jar ships no Sterling
  (verified against the oracle jar's contents), so every Sterling-shaped
  choice is a mettle design decision, never a conformance bug. The live
  lineage is `sidprasad/sterling-ts` (the fork Forge itself ships).
  Protocol: WebSocket, JSON `{type, version, payload}`, four message types
  (`data`/`click`/`eval`/`meta`) plus literal `ping`/`pong`; instance data
  travels as Alloy instance XML parsed per-`<instance>`-element (temporal
  traces natively understood); enumeration is not a protocol verb — the
  provider defines arbitrary `click` command strings; the evaluator pane is
  an opaque request/response string pair that maps almost 1:1 onto mettle's
  existing `ReplContext`.
- **The packaging survey** (memo, not a doc) landed a channel matrix and a
  concrete recommendation; its load-bearing local claims (zero C
  dependencies in the whole workspace, MPL-2.0, pinned rustc 1.97.0,
  dev-shell-only flake) were tech-lead-verified.

Three frictions the recon surfaced, which this ADR must route:

1. **The loop-attribute mismatch.** The jar writes `looplength = tracelength
   − loopState`; Sterling's parser reads `backloop` (falling back to
   `loop`) and never `looplength` — it was written against Forge's XML
   dialect, where the attribute appears to be the loop-state *index* (a
   second, unverified semantic difference). Byte-faithful jar XML fed to
   Sterling silently loses the loop point.
2. **No formal Sterling license.** No LICENSE file exists anywhere in the
   Sterling lineage; `sterling-ts` self-declares MIT only in
   `package.json`. Under ADR-0006's posture that is not a citable grant,
   so *embedding* upstream assets needs an owner decision first.
3. **The crates.io name `mettle` was registered by an unrelated project on
   2026-07-26**, blocking plain `cargo install mettle` / crates.io-backed
   `cargo-binstall` under the current name.

## Decision 1 — a jar-shape-exact instance-XML writer (mt-071)

mettle grows an instance-XML writer in `als-instance`, implementing
[alloy6-instance-xml.md](../reference/alloy6-instance-xml.md) exactly:

- **Replicate the reference writer's shape in full**, including the
  lazy-memoized touch-order ID scheme and the `macros` mechanism
  (`m<i>` skolems + the extra-instance blocks). Both are pinned,
  deterministic, and no harder to write correctly than a "simpler" scheme
  once the contract exists — and replicating them keeps the drop-in story
  clean (a human diffing `mettle`-written XML against jar-written XML for
  the same instance should see the same shape) and avoids a ledger entry.
  Where exact parity is genuinely impractical, the divergence gets a
  SEMANTICS_LEDGER entry, not a silent simplification (the mt-062/LEDGER-012
  precedent: shapes exact, live-order tuple content).
- Surfaced as `mettle exec … --xml <path>` (flag shape finalized in the
  bead spec) and as a library seam `als-instance` exposes for `serve`.
- **Verification is differential**: beyond jar-free shape tests, mt-071
  feeds mettle-written XML to the *jar's own* `A4SolutionReader.read` via
  the existing `XmlProbe` round-trip harness — closing, in passing, the
  reference doc's unpinned corner that round-trip acceptance was only
  exercised on the two simplest shapes.

## Decision 2 — `mettle serve` speaks Sterling's provider protocol (mt-072)

`mettle serve <file.als>` becomes the visualization entry point: one Rust
process serving the frontend's static assets over HTTP and the Sterling
provider protocol over WebSocket (single listener/port if the frontend's
`?<ws-address>` query mechanism permits — probed at implementation, not
assumed), wired to machinery that already exists:

- `data` = mt-071's XML (with the Sterling loop-attribute adaptation, below);
- `eval` = `ReplContext::eval_input` (per-state on temporal traces, mt-068);
- `click` verbs = mettle-defined enumeration commands: next-instance for
  static commands rides the existing `InstanceEnumerator`; the temporal
  fork/init/config operators stay **typed defers** until the trace-enumeration
  bead (already the STATE.md-tracked future bead) — buttons absent or
  greyed with an honest message, never wrong traces.
- **The Sterling XML dialect is an adapter, not a fork of the writer**: the
  serve path takes jar-exact XML and adds/rewrites the `backloop`
  attribute; the `--xml` export path stays byte-jar-exact. The `backloop`
  semantic question (loop-state index vs. `looplength`-style distance) is
  **pinned by a live-Sterling experiment as mt-072's opening probe**, along
  with sterling.md §9's other opens (does the trace stepper render
  multi-instance data; can the two ports collapse). No implementation until
  those cells are pinned — the house contract-first rule, scoped small
  because the protocol itself is already pinned.
- The HTTP/WS server dependency (the workspace's first runtime network
  dependency) is chosen in the mt-072 spec with the standing written
  justification per dependency; the strong prior is the smallest
  well-audited thing that does HTTP + WS upgrade correctly, not a
  framework.

Sterling conformance posture, stated once: **the scorecard never sees any
of this.** The jar has no Sterling and no serve verb; sterling.md is an
external contract. Divergences from *Sterling's* expectations are bugs
against mt-072's own spec; divergences from the *jar's* XML are governed by
Decision 1.

### Amendments (mt-072, 2026-07-27 — as implemented, tech-lead approved)

Three things this decision left to the implementation, recorded here because
each is a standing contract the frontend (mt-075) and the trace-enumeration
bead (mt-076) both build against.

**(a) A fifth outgoing message type, `error`.** The pinned protocol gives a
provider no channel to refuse anything: §2.2's four types are `data`, `click`,
`eval` and `meta`, and none of them can carry "I could not do that." Yet a
`click` on an unimplemented verb, an exhausted enumeration, and an unparseable
frame all need an answer — silence and a dropped connection are the two things
STYLE E5 forbids. mettle therefore sends `{"type":"error","version":1,
"payload":{"code","message"}}`, with `code` a stable machine-readable string
(`unknown-click`, `not-yet-supported`, `no-more-instances`,
`malformed-message`, `bad-payload`, …) and `message` one finished sentence.
This is **verified safe for external Sterling**: `sterling-connection`'s
`receive/onMessage.ts` dispatches on exactly `data`/`eval`/`meta` and falls
through silently on anything else, so an upstream client sees a no-op where
mettle's own frontend sees a diagnosable failure. It is the only place mt-072
extends the pinned shapes.

**(b) The `click` verb strings.** Enumeration is not a protocol verb (§2.3:
`onClick` is an opaque provider-defined string), so mettle defines five —
`next`, `next-trace`, `next-config`, `new-init`, `new-fork` — named after the
reference GUI's own exploration commands rather than Forge's `next`/`next-P`/
`next-C`. The divergence is deliberate: mettle's frontend is the first-party
consumer, nothing in the protocol requires matching Forge, and a self-
describing string is worth more than wire-compatibility with a provider mettle
never talks to. Only `next` is implemented; the four temporal verbs are
accepted on the wire and answered with a typed refusal naming mt-076, while a
temporal session offers **no buttons at all** (the "absent, never wrong"
half of the bullet above).

**(c) The runtime dependency shape, as landed.** `tungstenite` with
`default-features = false` (framing only), plus `serde`/`serde_json` — which
enter the *shipped* binary here for the first time, having been gauge-only via
`als-conform`. Explicitly **no async runtime and no HTTP framework** (STYLE
P4): the server is one hand-rolled `std::net::TcpListener`, thread per
connection via `std::thread::scope`, with the session behind a `Mutex`.
**Single port**, routed on the `Upgrade` header rather than the path — which
sidesteps §2.1's two-server query-string handoff for our own frontend
(`/ws` on the page's origin) while still letting an external Sterling upgrade
on `/` for free. Turning tungstenite's `handshake` feature off cost the
`Sec-WebSocket-Accept` derivation, which is now mettle's own (~130 lines of
SHA-1 + base64, pinned against FIPS 180-4's and RFC 4648's published vectors
as well as RFC 6455 §1.3's worked example); it is not a security primitive and
is documented as such. That trade removed eleven transitive crates (`http`,
`httparse`, `data-encoding`, `sha1` and its `digest` tail) from a workspace
that hand-writes its own CDCL solver — the framing layer is worth a
dependency, a fixed-GUID echo is not.

### Amendment (mt-075, 2026-07-27 — as implemented, tech-lead approved)

**(d) An optional `state` on the `click` payload.** mt-072 shipped "New Fork"
reading the state to fork after from the **evaluator pane**, because §2.3's
`click` payload carries nothing but a verb string and the reference's own
`VizGUI`/`OurConsole` share one `current` index anyway. mt-075's frontend
breaks that arrangement's one assumption: a temporal `data` payload is the
*whole* lasso, so its trace stepper moves between states entirely client-side,
with no evaluator round trip to observe. The payload therefore grows one
optional integer field, `state` — **`new-fork` uses it as the displayed-state
index (forking at `state + 1`, the pinned GUI semantics); every other verb
ignores it; and its absence keeps the mt-072 behaviour exactly**, so an
external Sterling, which will never send it, still gets the evaluator-pane
reading. A `state` outside the displayed trace is a typed refusal
(`state-out-of-range`), not a guess. Like amendment (a) this is additive on the
wire and invisible to an upstream client, which builds its own `click` payload
and would simply never populate the field. mettle's own frontend also keeps the
pane in step, sending the REPL's `:state N` before it evaluates an expression at
a stepped state — so the two indices agree in the direction the protocol cannot
express, exactly as they do in the reference GUI.

## Decision 3 — frontend assets: owner fork (A/B/C), recommendation B

How `mettle serve` gets a frontend, given the missing license grant:

- **(A) Embed the prebuilt `sterling-ts` bundle now** (~5.9 MB zipped,
  ~18 MB unzipped, mostly Monaco for a script view we don't need),
  treating the `package.json` MIT self-declaration + Forge's own
  redistribution as sufficient signal, and adding a NOTICE file (ADR-0006
  addendum). Fastest to the Rung-5 bar; weakest license footing.
- **(B) Ask upstream for a formal LICENSE first** (a one-file PR/issue to
  `sidprasad/sterling-ts`); meanwhile mt-072 ships the provider protocol
  end-to-end, testable against a locally-run Sterling ("bring your own
  Sterling" — a dev posture, not the shipped UX). Embed (flipping to A,
  possibly with a trimmed bundle) the moment the grant lands; fall back to
  (C) if refused or ignored on a timescale the owner sets.
- **(C) Write mettle's own minimal frontend** against the pinned protocol
  only (graph/table + evaluator). Cleanest licensing (a wire protocol is
  not copyrightable — the ADR-0006 stdlib posture), smallest binary,
  most work by far.

**Tech-lead recommendation: (B).** It unblocks all engineering now, keeps
ADR-0006 intact, and converts to the fast path the moment upstream answers.
Consequence to name honestly: **the Rung-5 exit gate ("no docs, under a
minute") cannot close until the fork resolves** — (B) is a bet that it
resolves quickly. This goes to the owner as a decision, not a status line.

## Decision 4 — packaging: cargo-dist spine + nix flake output (mt-073, mt-074)

- **mt-073**: adopt `cargo-dist` (verified actively maintained) as the
  release spine — GitHub Releases for macOS/Linux × aarch64/x86_64 (all
  native GA runners; the zero-C-dep workspace needs no cross toolchain),
  generated shell + PowerShell installers, a `chaychoong/homebrew-mettle`
  tap formula, and GitHub Artifact Attestations (the current signing norm;
  no key custody). Homebrew *core* is explicitly out (notability bar);
  Windows explicitly deferred (nothing forecloses it).
- **mt-074**: add `packages`/`apps` outputs to the existing flake so
  `nix run github:chaychoong/mettle` works, resolving the already-flagged
  rustc-1.97.0-vs-nixpkgs pin gap (rust-overlay or exact-toolchain fetch —
  the flake must build the *same* pinned toolchain as everything else;
  the project's determinism value applies to release builds too).
- Both beads land only after the workspace version leaves `0.0.0`, which
  happens at the Rung-5 exit gate, not before.
- The moment any third-party web assets are embedded (Decision 3 A-path),
  ADR-0006 §5's "no third-party text, no NOTICE file" claim goes stale —
  the embedding bead owns updating it. Named here so it cannot drop
  between the Sterling and packaging beads.

## Decision 5 — crates.io: skip for v1; the name question is the owner's

`cargo install mettle` now installs someone else's crate. Plain
`cargo install` was already the weakest channel for the Rung-5 bar (needs
a toolchain, misses "under a minute" cold); the recommended channels
(Releases + installers + tap + flake) don't touch the crates.io name. So:
**no crates.io publication in v1**, and the standing question — keep the
binary/product name and never publish to crates.io, publish under a
variant name (`mettle-analyzer`, …), or pursue the crates.io name-dispute
process — goes to the owner with no deadline attached. cargo-binstall
support (crates.io-backed) defers with it.

## Consequences

- Bead cut and order: **mt-071 → mt-072** (writer feeds serve); **mt-073 →
  mt-074** independent of both, gated on the version/exit decision. The
  Decision-3 fork shapes mt-072's *final* deliverable but not its start.
- The scorecard does not move during any of this (as at the mt-061/062
  slice — deliberate, disclosed). Rung 5's gauge is the ROADMAP row's
  human test, not the scorecard.
- Temporal trace *enumeration* (New Trace/Init/Fork parity) remains a
  future bead; `serve` presents its absence honestly rather than
  approximating it.
- [reference/alloy6-instance-xml.md](../reference/alloy6-instance-xml.md)
  becomes the third leg of the instance-surface authority set
  (alongside the evaluator and temporal §(f) docs); its "Unpinned" tail is
  mt-071's probe debt, mirrored there, with the round-trip corners closed
  by mt-071's own differential verification.

## Resolutions (2026-07-27, owner — same day as filing)

The owner resolved both forks and reshaped the cadence in one exchange:

1. **Decision 3 → option (C), browser-first.** mettle writes its **own
   minimal frontend** (graph + table views, trace stepper, evaluator pane)
   with a deliberate modern design pass, delivered in v1 as a web app
   served by `mettle serve` and opened in the user's browser — **not** a
   Tauri desktop app (owner floated Tauri; tech-lead recommendation
   browser-first was adopted: the visualization work is identical web code
   either way, and a Tauri shell can wrap the same frontend later as a
   small additive bead without app-bundle/notarization/webview costs now).
   **The pinned Sterling wire protocol is retained as `serve`'s protocol**
   ([reference/sterling.md](../reference/sterling.md)) — already pinned,
   fits exactly, and any external Sterling can still connect as free
   interop; the license question evaporates for shipped code (nothing
   upstream is embedded; a wire protocol is not copyrightable — the
   ADR-0006 stdlib posture). mt-072's formerly-gating live-Sterling probe
   demotes to a best-effort interop spot-check (the `backloop` dialect
   adapter serves external Sterling clients only, never our own frontend).
   New bead **mt-075** carries the frontend.
2. **Decision 5 → skip crates.io outright, not just for v1.** mettle is a
   binary product; the `als-*` crates are internal implementation, not a
   library offering, so nothing needs the squatted name and no rename or
   dispute is warranted. Revisit only if the project ever decides to ship
   libraries — a fresh naming decision then.
3. **Cadence: all human tests batch to one combined feature-complete
   review** (owner, superseding per-rung gating from here forward — the
   Rung-6 gate and the `check … for 1 steps` fork ride along to that
   review; engineering gates continue every chunk unchanged). **The
   feature-complete bar includes instance/trace enumeration** (the GUI's
   Next / New Config / New Init / New Fork parity + temporal counting on
   the scorecard) — new bead **mt-076**, cut into the set. Estimated
   distance at resolution time: ~6–9 chunks across mt-071/072/075/076/073/074.
