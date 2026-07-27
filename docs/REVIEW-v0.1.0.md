# The combined feature-complete review (v0.1.0)

> The one batched human review that replaced per-rung gating (owner decision,
> 2026-07-27, [ADR-0016](adr/0016-rung5-remainder-serve-xml-packaging.md)
> Resolution 3). Everything below is owner-runnable, copy-paste, ~20–30
> minutes. It bundles: the release-channel check (the Rung-5 "fresh install →
> visualized instance in under a minute" bar), the Rung-6 temporal gate
> ([ADR-0015](adr/0015-rung6-temporal-architecture.md) → Accepted on
> blessing), the full first-party frontend, and the one genuine fork decision
> still open. This doc is one-shot: after the review, fold the verdict into
> STATE.md and mark this file done.

Everything engineering-side is already verified green: v0.1.0 is released
with all four platform archives + shell installer, the Homebrew formula is
live on `chaychoong/homebrew-tap` (installed, smoked, and uninstalled on this
machine), the Docker image is published to GHCR, and CI is green on the tag.

## 0. Release plumbing — all done, no chores

Both owner chores closed 2026-07-27: the `HOMEBREW_TAP_TOKEN` secret exists
and the re-run v0.1.0 release went green end-to-end (all builds, `host`,
`publish-homebrew-formula` — the axo-bot formula commit landed on the tap
and was install-verified — and `announce`). The container image is public
and pull-verified. Every future `v*` tag publishes fully automatically.
Gotcha for other machines: a stale `docker login ghcr.io` credential makes
GHCR return `denied` even for public images; `docker logout ghcr.io` fixes
it.

## 1. Fresh install → visualized instance in under a minute (the Rung-5 bar)

Start a timer. Pick any channel (brew is the one verified end-to-end):

```sh
brew install chaychoong/tap/mettle
# or:  curl --proto '=https' --tlsv1.2 -LsSf https://github.com/chaychoong/mettle/releases/download/v0.1.0/mettle-installer.sh | sh
# or (after chore 2):  docker run --rm -p 4030:4030 ghcr.io/chaychoong/mettle serve --bind 0.0.0.0 <file>
```

Then, with no repo checkout at all:

```sh
mettle -V        # expect: mettle 0.1.0
cat > /tmp/meetings.als <<'EOF'
abstract sig Person {}
one sig Alice, Bob, Carol extends Person {}
sig Meeting { organizer: one Person, attendees: some Person }
fact { all m: Meeting | m.organizer in m.attendees }
run { some m: Meeting | #m.attendees > 2 } for 3
EOF
mettle serve /tmp/meetings.als
```

Open the printed URL. **Pass bar:** a solved, graph-rendered instance in the
browser, timer under a minute.

## 2. The Rung-6 temporal gate (blessing flips ADR-0015 to Accepted)

From the repo checkout (the corpus is local-only):

```sh
cargo build --release
./target/release/mettle exec corpus/alloytools-models/models/examples/temporal/trash.als
```

Look for: every command answered, full state-by-state traces in the jar's
shape with the loop marked, `VALID (no counterexample within N steps)`
wording for the checks.

Then the trace debugger:

```sh
./target/release/mettle exec corpus/alloytools-models/models/examples/temporal/trash.als --repl --command 0
```

At the prompt: `:state 1`, then `:state 5` (watch it wrap through the
lasso's loop), then evaluate a temporal expression live, e.g.
`always some Trash`.

## 3. The frontend, on a temporal model

```sh
./target/release/mettle serve corpus/alloytools-models/models/examples/temporal/trash.als --command 0
```

Worth poking at: graph view is the default (legend, per-sig hues,
subtractive focus); the **trace rail** draws the lasso's loop as an amber
arc; **New Trace / New Config / New Init / New Fork** all answer live
(mt-076's enumerator); the evaluator pane's `:state N` stays in sync with
the displayed state; the table-view toggle; dark/light; and it's fully
offline (no webfonts, no CDN).

## 4. ~~The one open fork: `check … for 1 steps`~~ — DECIDED (owner, mid-review 2026-07-27)

The owner chose **Option B: answer the length-1 check** — implemented same
day as **mt-077** ([LEDGER-015](../SEMANTICS_LEDGER.md)). The probe wave
run for the implementation also corrected the bug's pinned scope: the
jar's NPE is *not* `check`-specific (constant-folding `run`s crash too)
and most one-state `check`s answer fine — so the old refusal was itself a
divergence, and B increases conformance. Nothing left to decide here.

## 5. Verdict

Reply with: bless / findings per section (parts 1–3 are what remain).
Anything that looks like a divergence from Alloy fits the issue template
at `.github/ISSUE_TEMPLATE/divergence.md`. On blessing, the tech lead
flips ADR-0015 to Accepted, records the Rung-5/6 exits in
STATE/ROADMAP/TASKS, and marks this doc done.
