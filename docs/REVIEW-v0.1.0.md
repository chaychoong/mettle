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

## 0. Two one-click chores first (release plumbing only you can do)

1. **`HOMEBREW_TAP_TOKEN`** — create a fine-grained PAT with **Contents:
   read & write** on `chaychoong/homebrew-tap`, add it as an Actions secret
   named `HOMEBREW_TAP_TOKEN` on `chaychoong/mettle`. Until it exists, each
   tag's `publish-homebrew-formula` job fails red with `Input required and
   not supplied: token` (v0.1.0's formula was published by hand, so
   `brew install` already works today). Once the secret exists, "Re-run
   failed jobs" on the v0.1.0 release run exercises the automated publish
   end-to-end — the re-cut tag's workflow targets the right tap.
2. **Make the container image public** — the GHCR package defaulted to
   private on first publish, so anonymous `docker pull` is denied. Go to
   <https://github.com/users/chaychoong/packages/container/mettle/settings>
   → Danger Zone → Change visibility → Public.

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

## 4. The one open fork: `check … for 1 steps`

The jar NPE-crashes on exactly this shape (pinned, reproducible); mettle
cannot conform to a crash. Pick one:

- **(A) — recommended:** keep the typed `CANNOT EXECUTE` naming the jar
  bug. Strict drop-in posture, zero wrong-verdict risk. (This is what ships
  today.)
- **(B):** answer the length-1 check correctly — more useful, a deliberate
  scorecard-invisible divergence (the jar produces no verdict to compare).

## 5. Verdict

Reply with: bless / findings per section, plus the A-or-B call. Anything
that looks like a divergence from Alloy fits the issue template at
`.github/ISSUE_TEMPLATE/divergence.md`. On blessing, the tech lead flips
ADR-0015 to Accepted, records the Rung-5/6 exits in STATE/ROADMAP/TASKS,
and marks this doc done.
