Status: PINNED as recon (mt-070, tech-lead reviewed 2026-07-27 — the `backloop`-vs-`looplength` and no-LICENSE finds re-verified against the clones). **External-tool contract, NOT jar-pinned authority** — the oracle jar ships no Sterling, so nothing here is a conformance surface. §9/§10's open cells are closed by mt-072's opening live-Sterling probe; the license fork is [ADR-0016](../adr/0016-rung5-remainder-serve-xml-packaging.md) Decision 3 (owner).

# Sterling — the web visualizer, integration recon (mt-070)

This document pins **what Sterling is today, exactly how its provider
protocol works, and what mettle's own jar-pinned contracts already conflict
with it on** — the reconnaissance mt-070 needs before scoping `mettle
serve` into implementation beads. Unlike the other docs in this directory,
Sterling is a **third-party open-source tool, not the reference oracle**:
nothing here is pinned by `oracle/org.alloytools.alloy.dist.jar`, and (per
§3) the oracle jar doesn't contain Sterling at all. Facts below are tagged
`[VERIFIED: <citation>]` (a GitHub source file, a jar-inspection command, or
a fetched doc page) or `[INFERENCE]`. Anything not nailed down is in
[§9 Open questions](#9-open-questions) or [§10 Unverified](#10-unverified).

Primary source for the protocol section (§2) is
`sidprasad/sterling-ts` (shallow-cloned to
`scratchpad/probe/mt070/sterling/sterling-ts-sidprasad/`, git-ignored) —
see [§1](#1-what-sterling-is-today-the-ecosystem-map) for why this is the
repo to target — cross-checked against the provider-side reference
implementation in `tnelson/Forge`'s `forge/server/forgeserver.rkt` and
`forge/server/modelToXML.rkt` (raw-fetched, same scratch directory).

---

## Summary

- **Target this repo:** `sidprasad/sterling-ts` (project name "Cope and
  Drag" / "Spytial Sterling" — a fork of the original Sterling that adds
  spatial-layout scripting). It is the only actively-maintained lineage
  (pushed 2026-04-17) and is what Forge (the actively-maintained sibling
  Alloy-family tool) ships today. The original `atdyer/sterling` and the
  `alloy-js` org's `sterling`/`sterling-ui`/`sterling-js` repos are all
  stale since 2021-2022.
- **Protocol:** WebSocket, JSON envelope `{type, version, payload}`, 4
  message types (`data`, `click`, `eval`, `meta`), `ping`/`pong` keepalive,
  reconnect-on-close. Fully pinned in §2, with exact TypeScript source and
  a cross-check against Forge's own Racket-side handler.
- **Instance format:** the same Alloy instance XML schema mettle already
  writes (or will write) — `<instance>`/`<sig>`/`<field>`/`<skolem>`/
  `<type>`/`<tuple>`/`<atom>` with `label`/`ID`/`parentID` — **with one
  confirmed, load-bearing attribute-name mismatch**: mettle's jar-pinned
  contract uses `looplength`; Sterling's parser reads `backloop`/`loop`.
  See §2.4 and §6.
- **Not a conformance target.** The reference jar (6.2.0) ships zero
  Sterling code — only the classic Swing `VizGUI`. Sterling support is a
  mettle-only feature; divergences from any Sterling behavior are a mettle
  design choice, not a conformance bug. See §3.
- **Temporal traces are understood** natively by the parser (multiple
  `<instance>` elements per XML document, one per state) and Forge's UI
  distinguishes "next trace" from "next config" via two separate buttons —
  but this is provider-defined convention riding on the generic `click`
  message, not a protocol-level "next" verb. See §4.
- **Evaluator hook maps cleanly** onto mettle's existing REPL/evaluator:
  `eval` request carries `{id, datumId, expression}`; response carries
  `{id, result}` — both opaque strings. See §5.
- **Build/vendoring:** prebuilt release zips exist
  (`sterling-alloy.zip`/`sterling-forge.zip`, ~5.9 MB zipped / ~18 MB
  unzipped — heavy because it bundles Monaco editor workers for a
  scripting pane mettle likely doesn't need). Embeddable as static assets
  in a Rust binary (e.g. `rust-embed`) with no Rust-side dependency on the
  JS toolchain, **if trimmed** to drop the Script View. **License is a
  genuine open question**: no LICENSE file exists anywhere in the entire
  Sterling lineage; `sidprasad/sterling-ts`'s `package.json` self-declares
  `"license": "MIT"` but there is no formal grant to point to. See §7.
- **Recommendation-relevant tradeoffs and what still needs a live
  experiment:** §8 and §9.

---

## 1. What Sterling is today — the ecosystem map

`[VERIFIED: GitHub API + repo READMEs, see below]`

| Repo | Org | Stack | Last push | License file? | Status |
|---|---|---|---|---|---|
| `atdyer/sterling` | Tristan Dyer | Java (Gradle+Shadow) backend using Spark webserver, + a `public/` JS frontend | 2021-06-16 | none | Original; built against **Alloy 5.0.0.1** — pre-dates Alloy 6 `var`/temporal entirely |
| `alloy-js/sterling` | alloy-js org (successor org, same author) | same Java/Spark backend | 2021-06-16 | none | Mirror/rename of the above; org-level, not independently developed further |
| `alloy-js/sterling-ui` | alloy-js | React + Create-React-App, TypeScript | 2022-02-10 | none, no `license` field | A React-frontend rewrite attempt; superseded |
| `alloy-js/sterling-js` | alloy-js | JavaScript | 2022-09-30 | none | Small utility lib; last touched with the rest of the org |
| `alloy-js/alloy-ts` | alloy-js | TypeScript, "Alloy instances in TypeScript" | 2022-07-20 | **MIT** (declared) | An earlier standalone Alloy-XML-parsing library; superseded in the current lineage by `sterling-ts`'s own `alloy-instance` package |
| **`sidprasad/sterling-ts`** | Siddhartha Prasad (Brown) | TypeScript monorepo (React, Redux Toolkit, D3, Monaco), Vite/Webpack | **2026-04-17** | none in repo; `package.json` says `"license": "MIT"` | **Active, current lineage.** Published under the project name "Cope and Drag" (CnD) — a fork of Sterling that adds spatial-layout scripting. This is the exact zip `tnelson/Forge`'s `forge/sterling/update-sterling.sh` downloads by default (`DEFAULT_REPO="sidprasad/sterling-ts"`, `DEFAULT_ASSET="sterling-forge.zip"`). |

`[VERIFIED: GitHub API pushed_at/license fields queried 2026-07-27 via
`curl https://api.github.com/repos/<org>/<repo>` and
`https://api.github.com/orgs/alloy-js/repos`]`

**Docs sites found:** `sterling-js.github.io` (old domain) and
`alloy-js.github.io` (current domain for the same org) both serve a
`/tour` and `/about` — both describe Sterling 1.0 as "in preview" circa
February 2020 and contain no protocol-level technical documentation; they
are marketing/overview pages, not API references
`[VERIFIED: WebFetch of both URLs, 2026-07-27]`.
`sterling-ts-sidprasad`'s own `packages/sterling-connection/README.md`
points at `https://sterling-docs.vercel.app/sterling-connection/introduction`,
but that URL currently resolves to an unrelated site (some other project's
docs, apparently squatting the same Vercel subdomain) — **the linked docs
site is dead/repurposed** `[VERIFIED: WebFetch, HTTP 404 on the
sterling-connection page, unrelated content on the root, 2026-07-27]`. This
means **the TypeScript source itself is the only authoritative
documentation** for this lineage; §2 below is read directly from it.

**Recommendation for mettle:** target `sidprasad/sterling-ts`
(`sterling-forge.zip` or `sterling-alloy.zip` release asset — see §7 for
which). It is the only lineage with recent commits, the only one Forge
(the sibling tool with essentially the same integration problem mettle
has) ships today, and its `alloy-instance` XML parser is a superset of
what the older `alloy-ts` library did.

---

## 2. The provider protocol, exactly

`[VERIFIED: sterling-ts-sidprasad/packages/sterling-connection/src/*.ts,
cross-checked against tnelson/Forge/forge/server/forgeserver.rkt]`

### 2.1 Transport

WebSocket. The frontend SPA is served by one HTTP server (static assets);
a **separate** WebSocket server is the "data provider." The WS URL is
derived from the query string of the page the SPA itself was loaded from:

```ts
// packages/sterling-connection/src/middleware.ts
function getWebSocketURLFromLocation() {
  return `ws://localhost:${window.location.search.slice(1)}`;
}
```

So if Sterling's static assets are served at `http://localhost:4000` and
the user is sent to `http://localhost:4000?1234`, the SPA connects its
WebSocket to `ws://localhost:1234`. This is confirmed from the provider
side in Forge, which runs two independent servers and threads the
provider's ephemeral port through as the static server's query-string
parameter:

```racket
;; forge/server/forgeserver.rkt
(define-values (stop-service port)
  (start-websocket-server (get-option the-run 'sterling_port) handle-json))
;; ... serve the static sterling website files (this will be a different server/port)
(serve-sterling-static #:provider-port port
                        #:static-port (get-option state-for-run 'sterling_static_port))
```

`start-websocket-server` accepts port `0` for an ephemeral port
(`#:port port-option #:confirmation-channel chan`), so Forge doesn't have
to pre-reserve a fixed port. **Implication for `mettle serve`:** the same
two-server, query-string-handoff shape is required — mettle can't simply
open one HTTP+WS server on one port and expect the stock Sterling frontend
to find it; the frontend's WS-URL derivation is hardcoded to read the page
query string, not a runtime config file or an HTML `<meta>` tag
`[VERIFIED: same middleware.ts — no other URL-source code path exists in
this file]`.

Keepalive: after connecting, the frontend sends the literal string
`"ping"` every 3000ms and expects the literal string `"pong"` back
(not JSON-wrapped); Forge's handler special-cases this before the
JSON dispatch:

```racket
(cond [(equal? m "ping") (send-to-sterling "pong" #:connection connection)]
      [else (handler-proc connection m)])
```

Reconnect: on WS close, the frontend retries every 1000ms
(`RECONNECT_INTERVAL`) indefinitely `[VERIFIED: middleware.ts]`.

### 2.2 Message envelope and the 4 message types

```ts
// packages/sterling-connection/src/message.ts
export type MessageType = 'click' | 'data' | 'eval' | 'meta';
export type Msg<P = any> = { type: MessageType; version: number; payload?: P };
```

All messages are JSON-serialized `Msg` objects sent as WS text frames
(`JSON.parse`/`JSON.stringify`, no binary framing). `version` is currently
`1` on every outgoing message in both the TS client and the Forge server
(`'version 1` in every `newSend*Msg` call site and every `make-sterling-*`
Racket constructor) — there is no version negotiation handshake; it's a
static field both sides currently hardcode to `1` `[VERIFIED: message.ts
`newSend*Msg` functions + forgeserver.rkt `make-sterling-*` functions]`.

| type | direction | payload | when sent |
|---|---|---|---|
| `data` | Sterling → provider | none | on connect/reconnect, or whenever the UI explicitly asks to refresh |
| `data` | provider → Sterling | `DataJoin` (`enter`/`update`/`exit` arrays of `Datum`/`DatumMeta`) | in response to a `data` request, or after a `click` that produces a new instance |
| `click` | Sterling → provider | `Click` (`{id, onClick, context?}`) | user clicks a `Button` attached to a `Datum` (see §2.3, §4) |
| `eval` | Sterling → provider | `EvalExpression` (`{id, datumId, expression}`) | user submits an expression in the evaluator pane |
| `eval` | provider → Sterling | `EvalResult` (`{id, result}`) | provider's response to the above |
| `meta` | Sterling → provider | none | requesting provider capabilities |
| `meta` | provider → Sterling | `ProviderMeta` (`{name?, evaluator?, views?, generators?, features?}`) | provider's self-description |

`[VERIFIED: packages/sterling-connection/src/payload.ts,
packages/sterling-connection/src/message.ts]`

### 2.3 The `Datum`/`Button` shape — how the provider drives the UI

```ts
// packages/sterling-connection/src/types.ts
export interface Datum {
  generatorName: string | undefined; // e.g. a run/check name
  id: string;                        // unique id, provider-assigned
  format: string;                    // 'alloy' | 'raw' (only two the client parses)
  data: string;                      // the raw payload — Alloy instance XML for format='alloy'
  buttons?: Button[];                // arbitrary provider-defined action buttons
  evaluator?: boolean;               // whether this datum supports eval
}
export interface Button {
  text: string;      // button label
  onClick: string;   // opaque string echoed back in the next Click payload
  mouseover?: string; // tooltip
}
```

The client only recognizes two `Datum.format` values: `'alloy'` (parsed by
`parseAlloyXML`, §2.4) and `'raw'` (passed through as a plain string,
unparsed) — any other format value produces a dispatched `sterlingError`
and the datum is dropped `[VERIFIED: packages/sterling-connection/src/parse/parse.ts
`formatIsSupported`]`.

There is **no protocol-level "next instance" verb**. Buttons are entirely
provider-defined: the provider attaches whatever `Button`s it wants to a
`Datum`, and when the user clicks one, Sterling sends back a `click`
message with that exact `onClick` string in the payload. The provider is
responsible for interpreting the string. See §4 for the exact strings
Forge uses.

### 2.4 The Alloy XML instance format, exactly what's load-bearing

```ts
// packages/alloy-instance/src/xml.ts — parseAlloyXML(xml: string)
const instances = Array.from(document.querySelectorAll('instance'));
// ... one AlloyInstance object per <instance> element ...
return {
  instances: instances.map(instanceFromElement),
  bitwidth:    parseNumericAttribute(instances[0], 'bitwidth'),
  command:     parseStringAttribute(instances[0], 'command'),
  loopBack:    parseNumericAttribute(instances[0], 'backloop')
            ?? parseNumericAttribute(instances[0], 'loop'),   // NOT 'looplength'
  maxSeq:      parseNumericAttribute(instances[0], 'maxseq'),
  maxTrace:    parseNumericAttribute(instances[0], 'maxtrace'),
  minTrace:    parseNumericAttribute(instances[0], 'mintrace'),
  traceLength: parseNumericAttribute(instances[0], 'tracelength'),
};
```

Per-`<instance>` parsing (`instanceFromElement`) is applied **independently
to every `<instance>` element** in the document — it builds a fresh
`{types, relations, skolems}` from that element's own `<sig>`/`<field>`/
`<skolem>` children via `querySelectorAll`, scoped to that element. This
means:

- **A document with multiple `<instance>` elements (a temporal trace) is
  natively understood** — each element becomes one entry in
  `AlloyDatum.instances[]`. This matches mettle's own already-pinned
  finding (`alloy6-temporal.md` §(f)) that the reference jar emits
  `tracelength`-many independent `<instance>` blocks, each re-emitting all
  rigid (non-`var`) content in full. Sterling's per-element parser doesn't
  care about `var`-vs-rigid distinction at all — it just re-parses
  whatever `<sig>`/`<field>` elements are present in each block, which is
  exactly what the jar's redundant-re-emission shape gives it for free.
- **The file-level metadata (`bitwidth`, `command`, loop info, `maxseq`,
  `maxtrace`, `mintrace`, `tracelength`) is read only from `instances[0]`**
  — the first `<instance>` element — not merged/validated across blocks.
  This is consistent with mettle's own finding that the jar repeats these
  attributes identically on every block, so reading only the first is safe
  *given jar-faithful XML*.
- **Confirmed attribute-name mismatch:** the parser reads `backloop`
  (falling back to `loop`) for the loop-state field, with an inline
  comment `// TODO: Remove this hack once forge is fixed`. It does **not**
  read `looplength` at all. mettle's own jar-pinned contract
  (`alloy6-temporal.md` §(f)) established that the *real* Alloy jar's
  `A4Solution.writeXML` writes `looplength="K"` (`K = tracelength -
  loopState`), not `backloop`. Cross-checking Forge's own XML writer
  (`forge/server/modelToXML.rkt` line ~165: `tracelength="2"
  backloop="1"`) confirms this parser was written against **Forge's**
  XML dialect, which diverges from mainline Alloy's on this one attribute
  name (both encode the same underlying value — `backloop`/`loop` in
  Forge's dialect appears to be the loop-state index rather than
  `tracelength - loopState`, which is a second, unverified semantic
  difference — see §10). **A mettle Sterling adapter that emits
  byte-faithful jar XML will have its trace's loop point silently ignored
  (`loopBack` parses to `undefined`) unless the adapter also writes (or
  rewrites) a `backloop` attribute.**

Per-`<sig>`/`<field>`/`<skolem>` element shape (standard Alloy XML, matches
what mettle's own pinned contract already assumes):

- `<sig ID="n" label="Name" parentID="m" [abstract|builtin|enum|meta|one|private]="yes">` containing `<atom label="..."/>` children (for scalar sigs) or `<type ID="..."/>` children (for sigs that are actually product/set relations rendered via a `<sig>` wrapper — `sigElementIsSet` checks for this)
- `<field label="Name">` containing `<type ID="..."/>` children (the field's column types, parent type first) and `<tuple>` children, each `<tuple>` containing ordered `<atom label="..."/>` children (one per column)
- `<skolem>` — same shape as `<field>`, for skolem relations produced by existentials

`[VERIFIED: packages/alloy-instance/src/{xml,instance,type,relation,tuple,atom}.ts]`

### 2.5 `visualizer` element — an out-of-spec extension

`parseAlloyXML` also looks for `<visualizer script="..." theme="..."
cnd="...">` elements anywhere in the document (last-one-wins per
attribute) and surfaces them as `visualizerConfig`. The source comment is
explicit that this is **not part of the Alloy instance XML spec** — it's
an extension this fork invented to let a provider embed a default D3
script / theme / CnD (Cope-and-Drag spatial layout) constraint alongside
the instance data `[VERIFIED: packages/alloy-instance/src/xml.ts, lines
10-23]`. Not needed for a first mettle integration; noted so it isn't
mistaken for a required element.

---

## 3. Alloy-side precedent — is Sterling a conformance target?

`[VERIFIED: unzip -l oracle/org.alloytools.alloy.dist.jar | grep -i
sterling` → **zero matches**, run 2026-07-27]

The pinned reference jar (`oracle/org.alloytools.alloy.dist.jar`, Alloy
6.2.0, per ADR-0002) contains **no Sterling code, no web assets, no
embedded HTTP/WebSocket server of any kind** beyond an unrelated LSP
server class (`org.alloytools.alloy.lsp.provider.AlloyLanguageServer`,
which is a text-editor language server, nothing to do with visualization).
Its only visualizer is the classic Swing GUI:
`edu.mit.csail.sdg.alloy4viz.VizGUI` and ~25 supporting classes
(`VizGraphPanel`, `VizCustomizationPanel`, `StaticGraphMaker`,
`StaticInstanceReader`, `MagicLayout`, etc.), all compiled `.class` files
with matching `help/*.html` (the classic Swing "Viz" help pages, e.g.
`help/viz.gif`, `help/vizview.html`).

Historically, `atdyer/sterling` (§1) shipped as **a custom, separately-
distributed build of Alloy 5.x** ("Alloy + Sterling") — bundling the
Sterling Java backend as an additional dependency on top of stock Alloy
5.0.0.1, not a patch to Alloy's own mainline distribution
`[VERIFIED: atdyer/sterling/build.gradle declares `alloy` as a dependency
rather than being built inside an Alloy fork; WebSearch result describing
it as "included in a custom build of Alloy"]`. That custom build pre-dates
Alloy 6's temporal semantics entirely (Alloy 5 has no `var`/lasso traces),
so even at its most active it never had to solve the multi-`<instance>`
trace problem mettle now has.

**Conclusion: Sterling support is a mettle-only feature, not a
conformance target.** The scorecard (mettle's one gauge, per CLAUDE.md) is
defined purely against solve/verdict/text-output behavior; there is no
Sterling-shaped entry in it, and there never will be one from the jar
side — any UI/protocol choice mettle makes for `mettle serve` is a mettle
design decision, reviewed against this recon doc and (once written) an ADR,
not against jar output.

---

## 4. Temporal/Alloy 6 traces in Sterling

`[VERIFIED: forgeserver.rkt lines ~138-270, cross-checked against §2.4]`

Forge's provider implementation (the only concrete provider-side reference
implementation available, since the jar has none) distinguishes two kinds
of "next" for temporal models, both riding the generic `click` message
with provider-chosen `onClick` strings:

```racket
(define temporal? (equal? (get-option the-run 'problem_type) 'temporal))
;; ...
'buttons (cond [(not not-done?) (list)]
               [temporal?
                (list (hash 'text "Next Trace"
                            'mouseover "(Keeps configuration constant)"
                            'onClick "next-P")
                      (hash 'text "Next Config"
                            'mouseover "(Forces different configuration)"
                            'onClick "next-C"))]
               [else
                (list (hash 'text "Next"
                            'mouseover "(Get next instance)"
                            'onClick "next"))])
```

Server-side dispatch on receipt:

```racket
(cond [(equal? onClick "next-C") (get-next-instance 'C)]
      [(equal? onClick "next-P") (get-next-instance 'P)]
      [(equal? onClick "next")   (get-next-instance)]
      ...)
```

`'C` and `'P` are modes passed to Forge's lazy solution tree
(`tree:get-child current-tree next-mode`) — `'P` walks to the next trace
with the same configuration/skeleton constrained, `'C` forces a genuinely
different configuration. **This maps directly onto Alloy's own "New
Config"/"New Trace" distinction** in the classic VizGUI's temporal
exploration menu (not independently re-verified against the jar in this
recon pass — flagged in §9) — i.e. this is very likely encoding a concept
Alloy 6 itself has, just exposed through Sterling's generic button
mechanism rather than a dedicated protocol verb.

**UI affordance for time projection / stepping through states within one
trace** (as opposed to solving for the *next distinct trace*) is not
visible anywhere in `forgeserver.rkt` — the multi-`<instance>` XML
document is handed to the client whole, and it's the client (the
`sterling`/`sterling-ui` frontend package, not `sterling-connection`)
that must render a state-by-state stepper/scrubber over
`AlloyDatum.instances[]`. This recon pass did not read the frontend
rendering code (`packages/sterling/`, `packages/sterling-ui/`) — flagged
as an open question in §9.

---

## 5. The evaluator hook

`[VERIFIED: payload.ts EvalExpression/EvalResult; sendEval.ts;
forgeserver.rkt eval-branch lines ~185-198]`

Request (`Sterling → provider`, `type: 'eval'`):

```json
{"type": "eval", "version": 1, "payload": {"id": "<expr-uuid>", "datumId": "<datum-id>", "expression": "<user's typed expression text>"}}
```

Response (`provider → Sterling`, `type: 'eval'`):

```json
{"type": "eval", "version": 1, "payload": {"id": "<same expr-uuid>", "result": "<string>"}}
```

Both `expression` and `result` are opaque strings — no structured AST or
typed value on the wire. Forge's handler evaluates via its existing
`evaluate-func` (the same evaluator used by its REPL/CLI) and stringifies
the result with `->string`; it also logs (but does not reject) a
stale-datum mismatch:

```racket
(when (not (equal? (->string datum-id) (->string curr-datum-id)))
  (printf "Error: Sterling requested outdated evaluator (id=~a; curr-id=~a); reporting back inaccurate data!" datum-id curr-datum-id))
```

i.e. Forge evaluates against whatever its *current* solve state is
regardless of which historical `datumId` the click came from, and merely
warns to its own log if they've drifted — it does not maintain per-datum
solver state to answer against an older instance. **This is directly
compatible with mettle's existing REPL** (`mettle exec --repl`, mt-062):
mettle already has `ReplContext`/`eval_input` taking a raw expression
string and rendering a string result (`docs/reference/alloy6-evaluator.md`).
Wiring `eval` messages to that same function is the cheap case flagged in
the mt-070 brief — the message shape requires no new evaluator work, only
a WebSocket handler that calls the existing entry point and returns its
existing string rendering.

`ProviderMeta.evaluator` is declared as a `string` in the TypeScript type
(`packages/sterling-connection/src/payload.ts`) but documented in its own
JSDoc as "whether the provider supports a REPL" and set to a boolean
literal (`#t`) by Forge's `make-sterling-meta` — **this is an inconsistency
in the upstream source itself** (type says `string`, JSDoc and only known
producer both say boolean), not something to resolve on mettle's side;
flagged in §10.

---

## 6. Enumeration hooks

Already covered in full in §2.3 (`Button`/`Click` mechanism) and §4
(Forge's exact `next`/`next-P`/`next-C` convention for static vs. temporal
models). There is no separate protocol-level enumeration message — this
answers the brief's Q6 directly: enumeration requests reach the provider
as ordinary `click` messages, and the *provider* — not the protocol —
defines what "next config"/"init"/"fork" mean. For mettle this means
`mettle serve`'s WebSocket handler owns the entire enumeration semantics;
it can reuse mettle's existing bounded-lasso solve driver (mt-067) and
temporal state-index model (mt-068) as its "next" implementations, with
button strings chosen to match Forge's convention (`next`, `next-P`,
`next-C`) for UI familiarity, or its own — nothing in the protocol
requires matching Forge's strings.

---

## 7. Build & vendoring story

`[VERIFIED: GitHub Releases API for sidprasad/sterling-ts; downloaded and
unzipped v2.5.4/sterling-forge.zip, 2026-07-27]`

Prebuilt static bundles exist as GitHub Release assets on
`sidprasad/sterling-ts`, two variants per release (`sterling-alloy.zip`,
`sterling-forge.zip` — built via `webpack --env provider=alloy` /
`--env provider=forge` respectively, per the repo's root `package.json`
`scripts`). Both variants are essentially the same size:

- `sterling-forge.zip` (release `v2.5.4`, 2026-04-03): **5,894,110 bytes**
  zipped, **~18 MB** unzipped.
- Contents: `index.html`, ~130 webpack `*.bundle.js` chunks (code-split),
  several `*.worker.js` files (`ts.worker.js`, `json.worker.js`,
  `css.worker.js`, `html.worker.js`, `editor.worker.js` — these are
  **Monaco Editor**'s web workers, pulled in for the Script View's
  in-browser code editor), woff/woff2/ttf font files, and a `vendor/`
  directory.

This is heavy for what mettle needs (instance visualization + evaluator),
almost entirely because of Monaco (a full VS-Code-grade code editor) for a
scripting feature mettle likely doesn't want in v1. **Options, not yet
decided:**

1. Ship the full prebuilt zip as-is, embedded via `rust-embed` or similar
   — simplest, but bakes an ~18 MB (uncompressed) asset payload into the
   binary for a feature-surface mettle mostly won't use.
2. Build a trimmed static bundle from source with the Script
   View/Monaco disabled — requires standing up the Node/webpack toolchain
   this repo uses (root `package.json` lists Blueprint, Chakra, D3,
   Redux Toolkit, Monaco, and more — a real frontend build, not a trivial
   one) as part of mettle's release process, or as a one-time asset
   snapshot committed like any other vendored static asset.
3. Fork the `sterling-connection`/`alloy-instance`/`sterling`/
   `sterling-ui` packages into a from-scratch, minimal Rust-served
   frontend that only implements the graph/table view + evaluator, reusing
   just the *protocol* (§2) rather than any of the upstream JS. Most work,
   smallest and most auditable result, and sidesteps the license question
   in §7's next paragraph entirely for the shipped frontend code (mettle's
   own protocol-handling Rust server code doesn't touch Sterling's
   copyright regardless of which option is chosen, since it's a clean-room
   reimplementation of a documented wire protocol — the same posture
   ADR-0006 already takes for the Alloy stdlib).

**License — a genuine open question, not yet resolved.** No LICENSE file
exists anywhere in the entire Sterling lineage checked
(`atdyer/sterling`, `alloy-js/sterling`, `alloy-js/sterling-ui`,
`alloy-js/sterling-js`, `sidprasad/sterling-ts`) — confirmed by `find
. -iname "LICENSE*"` in every shallow clone in
`scratchpad/probe/mt070/sterling/`, and by the GitHub license-detection
API returning `null`/404 for all of them except `alloy-js/alloy-ts`
(declared MIT) and, naturally, `tnelson/Forge` itself (declared MIT).
`sidprasad/sterling-ts`'s root `package.json` self-declares `"license":
"MIT"`, and Forge (itself MIT, actively maintained, code-reviewed by a
CS-education-facing university lab) both depends on it and redistributes
its build artifacts under that same posture — a reasonably strong signal
in practice, but **not a citable, formal grant** the way ADR-0006 wants
for anything mettle embeds. If mettle goes with option 1 or 2 above
(embedding the actual upstream build/source), this should be escalated
to the product owner as an ADR-0006 addendum before committing any
Sterling assets to the mettle repo, the same way the stdlib clean-room
question was — the safest fallback (already the direction option 3 leans)
is treating the *protocol* as the only thing mettle depends on (a wire
format is not copyrightable) and writing mettle's own frontend/served
assets from scratch.

---

## 8. Alternatives inventory (brief)

**Classic Swing `VizGUI`** (the jar's actual shipped visualizer,
§3). ~25 classes, ~200 KB of bytecode, tightly coupled to the jar's own
`AlloyInstance`/`AlloyModel`/`AlloyRelation` object model (not a
serialization format — direct Java object graphs) and to Swing's
`JGraph`-style rendering (`StaticGraphMaker`, `VizGraphPanel`,
`MagicLayout` for automatic layout, `VizCustomizationPanel` for the
per-run theme editor). Porting this to Rust would mean reimplementing a
whole desktop GUI toolkit's worth of custom graph-layout and theming code
with no web/CLI-first payoff — explicitly **not wanted**
(`LIMITATIONS.md`: "no native GUI (Sterling + CLI only)" is already a
pinned v1 non-goal); characterized here only so the option is visibly
considered and rejected, not silently skipped.

**Other maintained Alloy-family visualizers:** none found in this recon
pass beyond the Sterling lineage and the classic Swing GUI. Forge's own
frontend (`packages/sterling` in `sterling-ts-sidprasad`, and the
now-superseded `packages/sterling-ui`) *is* Sterling, not a separate tool
— Forge doesn't maintain an independent visualizer. No evidence surfaced
of e.g. a VS Code extension, a headless-diff tool, or another web
visualizer targeting Alloy 6 XML specifically; this was not exhaustively
searched (see §9).

---

## 9. Open questions

Things this recon pass could not settle from source-reading alone and
would need an actual running Sterling instance (or a deeper read of the
frontend rendering packages, which this pass didn't open) to answer:

1. **Does the frontend (`packages/sterling`, `packages/sterling-ui` in
   `sterling-ts-sidprasad`) actually render a state-by-state
   stepper/scrubber UI for a multi-`<instance>` trace datum, and if so
   what interaction triggers what?** §4 confirms the *data* format
   supports it and the *provider* can distinguish next-trace vs
   next-config, but this pass did not open the rendering-layer source to
   confirm the UI affordance exists and is wired up, only that the parser
   produces an `instances[]` array a renderer *could* step through.
2. **Does `next-P`/`next-C` actually correspond to Alloy's jar-side "New
   Trace"/"New Config" VizGUI menu items**, or is this Forge-specific
   terminology with no jar equivalent? Not independently re-verified
   against the jar's `VizGUI` bytecode/menu structure in this pass.
3. **Is there a `sterling_static_port`/`sterling_port` collision or
   single-port mode** available (i.e., can the static assets and the
   WebSocket both be served from one Rust `axum`/`warp` listener, or does
   the frontend's `getWebSocketURLFromLocation()` genuinely require two
   ports)? The code as read requires the query-string handoff, which
   *could* still work with same-host-different-port URLs constructed by a
   single Rust process listening on two sockets, or possibly a single
   socket doing protocol multiplexing if the frontend's dev-proxy pattern
   (mentioned in early search results, not verified in source) generalizes
   — not tested live.
4. **Exact behavior of Forge's `backloop` semantics** — is it literally
   the loop-*state* index (as `loop` was in older Alloy XML dialects
   pre-`looplength`) or is it `tracelength - loopState` like the jar's
   `looplength`, just under a different name? This determines whether a
   mettle adapter can emit `backloop="<jar's looplength value>"` directly
   or must compute a different number. Not verified — `modelToXML.rkt`
   was only grepped for attribute names, not read in full for the
   surrounding computation.
5. **Whether `sterling-alloy.zip` and `sterling-forge.zip` actually differ
   in any way that matters for mettle** (which one to base an adapter on)
   — both were observed to be nearly identical in size; the `--env
   provider=alloy`/`provider=forge` webpack flag's actual effect on the
   bundle was not traced.
6. **No exhaustive search was done for other Alloy 6-targeting
   visualizers** beyond what turned up in the searches run (§8) — a
   negative result here is weaker than the positive findings elsewhere in
   this doc.
7. **A live end-to-end experiment** (stand up the prebuilt
   `sterling-forge.zip`, point a minimal script/mock provider at it, watch
   real WS traffic) would firm up everything in §2 from "read from source"
   to "observed on the wire" — not done in this pass (scope was
   primary-source research, not a running experiment).

---

## 10. Unverified

- `ProviderMeta.evaluator`'s type (`string` in the TS type, boolean in
  practice per Forge's only known producer and the JSDoc) — flagged as an
  upstream inconsistency in §5, not resolved.
- The `visualizerConfig`/`<visualizer>` XML extension (§2.5) — read from
  source but not exercised against any real provider that emits it; Forge's
  `forgeserver.rkt` handler as read in this pass does not appear to emit
  `<visualizer>` elements (not confirmed by an exhaustive read of
  `modelToXML.rkt`, only a `tracelength`/`backloop` grep).
  `sidprasad/sterling-ts`'s license posture (§7) — `package.json` claims
  MIT, no LICENSE file confirms it; treat as unverified until either a
  LICENSE file appears upstream or the product owner is asked directly.
- Whether the classic Swing `VizGUI`'s "New Config"/"New Trace" menu
  actually exists and matches Forge's `next-C`/`next-P` naming (§9.2) —
  inferred from naming similarity only, not confirmed against jar
  bytecode/menu resources in this pass.

---

## Provenance

- Reference jar inspection: `unzip -l
  oracle/org.alloytools.alloy.dist.jar | grep -i sterling` (zero
  matches) and `| grep -i -e web -e viz` (VizGUI + help pages only, no web
  server classes) — run 2026-07-27 on the pinned oracle build (ADR-0002).
- `sidprasad/sterling-ts` shallow-cloned (`--depth 30`) to
  `scratchpad/probe/mt070/sterling/sterling-ts-sidprasad/` (git-ignored),
  commit at clone time = the `main` branch HEAD as of 2026-07-27.
- `atdyer/sterling` and `alloy-js/sterling-ui` shallow-cloned
  (`--depth 50`) to the same scratch directory for the ecosystem survey in
  §1.
- `forge/server/forgeserver.rkt` and `forge/server/modelToXML.rkt`
  raw-fetched from `tnelson/Forge`'s `main` branch (2026-07-27) rather than
  full-cloned (the Forge repo is large; only these two files were needed).
- GitHub REST API (`/repos/...`, `/orgs/.../repos`, `/repos/.../releases`,
  `/repos/.../license`) queried unauthenticated except where noted, via
  `curl`, 2026-07-27.
- `sterling-forge.zip` (release `v2.5.4`) downloaded and unzipped to
  `scratchpad/probe/mt070/sterling/bundle-check/` for the size
  measurement in §7.
- Cross-references into mettle's own already-pinned contracts:
  [alloy6-temporal.md §(f)](alloy6-temporal.md#f-trace-instance-rendering--xml)
  (the `looplength` finding this doc's §2.4/§6 conflicts with),
  [alloy6-evaluator.md](alloy6-evaluator.md) (mettle's REPL this doc's §5
  proposes wiring the `eval` message to), `LIMITATIONS.md` (the
  "Sterling/`serve` integration" and "no native GUI" lines this doc
  scopes and confirms), `docs/ROADMAP.md` Rung 5 (`mettle serve`, the
  feature this recon is for).

Full capture notes and cloned material:
`scratchpad/probe/mt070/sterling/` (git-ignored; see its `README.md` for
an index of what's there and how to reproduce each finding).
