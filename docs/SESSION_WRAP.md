# Session wrap-up routine

Run this before ending any working session, so the next one (or a cold clone) picks up with **zero context loss**. This is the counterpart to the pickup routine in [../CLAUDE.md](../CLAUDE.md) → "Start here". Keep it fast — most steps are one command.

## 1. Land the code
- [ ] `git status` is clean — every intended change committed, nothing stray. If something is intentionally left uncommitted, say why in `STATE.md`.
- [ ] No junk tracked: no `target/`, no `oracle/` jar, no secrets, no `exec` scratch output dirs. Sanity: `git ls-files | grep -Ei 'target/|\.jar$|/oracle/'` returns nothing.
- [ ] If code changed this session, the gates are green:
      `cargo build --workspace --all-targets && cargo fmt --all --check && cargo clippy --all-targets --all-features -- -D warnings && cargo test --workspace`.

## 2. Make the docs true
- [ ] **[STATE.md](STATE.md)** updated: `Last updated` date, current rung, what exists, **In flight** (running agents → how to resume, else "None"), **Next chunk** (concrete enough that a bare "proceed" is unambiguous), recent decisions, open questions.
- [ ] **[TASKS.md](TASKS.md)** beads match reality: statuses (✔/◐/▢/⛔) accurate, new beads added, dependencies noted, the next-on-"proceed" bead marked.
- [ ] Decisions made this session are recorded — a new/updated **[ADR](adr/)** for architecture/process calls; a **[SEMANTICS_LEDGER.md](../SEMANTICS_LEDGER.md)** entry for any pinned behavior (status proposed/verified/approved). *Nothing decided lives only in chat.*
- [ ] **[LIMITATIONS.md](../LIMITATIONS.md)** still honest (nothing newly supported left as "can't"; nothing claimed that isn't true).
- [ ] Every new doc is linked from **[README.md](README.md)** (nothing orphaned); superseded docs marked, not deleted.
- [ ] **[CLAUDE.md](../CLAUDE.md)** updated *iff* the operating model changed; still lean.

## 3. File the lessons
- [ ] Put each lesson where it will actually be read: reference/oracle gotchas → **[reference/](reference/)**; coding rules → **STYLE.md** / **PORTING_RULES.md**; cross-cutting/process lessons → **[LESSONS.md](LESSONS.md)**. Don't leave a hard-won lesson only in chat.
- [ ] Cross-session **memory** updated (`~/.claude/projects/.../memory/`): project status, key decisions, gotchas, what worked; prune anything now stale. (This is what a session started in the *website* dir sees.)

## 4. No loose ends
- [ ] No background sub-agent still running unnoticed — either finished-and-reviewed, or its state + resume instructions are in STATE.md "In flight".
- [ ] Downloaded/large/scratch artifacts are git-ignored, not committed.

## 5. (Optional) Verify the handoff
- [ ] For a big or uncertain handoff, dry-run it: a fresh-context, read-only agent given only the repo + "proceed" should name the right next task. Fix any gap it finds. (Used at the end of the foundations session; it caught an uncommitted-instruction gap.)

## 6. Final commit + sign-off
- [ ] Final commit(s): scopedcommits style (`scope(subscope): imperative title`), no AI attribution, reference bead ids (`mt-NNN`).
- [ ] One product-level closing message to the owner: what shipped, where we are on the roadmap, what "proceed" will do next, and anything needed from them.
