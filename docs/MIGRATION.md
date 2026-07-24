# Migration checklist

How to move the mettle working environment to a new machine (mt-042(d), owner-directed
2026-07-18) without losing state, and how to verify on arrival that the new box
reproduces the old one bit-for-bit. Companion to [SESSION_WRAP.md](SESSION_WRAP.md)
(the routine that gets the *old* box into a clean, migratable state) and
[reference/alloy6-reference.md](reference/alloy6-reference.md) /
[reference/corpora.md](reference/corpora.md) (what `scripts/bootstrap.sh` re-fetches).

**Status: living document.** Update the recorded hash (Phase 1) every time a code
change lands after it, per that section's note.

---

## Phase 1 — before leaving the old box

1. **Finish and land in-flight work.** Run the full [SESSION_WRAP.md](SESSION_WRAP.md)
   routine: gates green, `docs/STATE.md` / `docs/TASKS.md` true, lessons filed, final
   commit(s) made.
2. **Confirm a clean tree:**
   ```
   git status
   ```
   must report nothing to commit, nothing untracked that matters (junk check:
   `git ls-files | grep -Ei 'target/|\.jar$|/oracle/'` returns nothing — see
   SESSION_WRAP §1).
3. **Push everything** the new box will need to clone (see the git-workflow note in
   `docs/STATE.md`/memory — `origin` is the public GitHub remote; work happens on
   `main`, pushed after each chunk):
   ```
   git push origin main
   ```
4. **Record the last verified full-sweep report hash**, so arrival can byte-compare
   without re-deriving it from scratch. This is the determinism contract's
   reference point (Phase 3 step 5): the stage-1 solve-gauge sweep, at defaults,
   run with any `--jobs` count, must produce byte-identical stdout on any machine.

   | | |
   |---|---|
   | Command | `cargo build --release -p als-conform && ./target/release/solve-gauge --jobs N` (any `N`; defaults for everything else — 10,000 conflicts / 4,000,000 encode-budget / 20,000 primary-var cap / symmetry 20) |
   | stdout SHA-256 | `72ad3b3368ace33623ac83dac5be608128dfc47dc88b53196d2a50a585be9cf2` |
   | Recorded | 2026-07-22 (post-mt-053; supersedes the 2026-07-21 `c4f7f8ca…` hash). Re-verified byte-identical 2026-07-24 post-mt-041 on the Mac (the mt-041 change is verdict-invisible — stage-1 output unchanged) |
   | Commands / verdict | 564 commands, **agree 301** (166 SAT / 135 UNSAT), DISAGREE 0 |

   **This hash is only valid as of the commit it was recorded at.** Any code change
   landing after 2026-07-21 (encoder, evaluator, solver, gauge, budgets, corpus
   pins — anything that can move a verdict or reorder output) invalidates it. If
   you're reading this after such a change, **re-run the command above on the old
   box and re-record its hash here (and the date) before migrating** — otherwise
   Phase 3's cross-check has nothing valid to compare against.

## Phase 2 — the move

1. **Clone, then re-key the agent memory to the new path.** The Claude agent
   memory directory (`~/.claude/projects/<path-key>/...`) is keyed off the
   repo's absolute path; same-path cloning preserves it automatically, but a
   different path works fine (proven 2026-07-24, see the as-executed log):
   copy `memory/` under the new path's key and rewrite absolute paths inside
   the memory files. Current primary: `/Users/choong/repos/chaychoong/mettle`
   (key `-Users-choong-repos-chaychoong-mettle`).
   ```
   git clone git@github.com:chaychoong/mettle.git <repo-path>
   ```
2. **Move `~/.claude` once**, as a single rsync — this carries the agent memory
   (`~/.claude/projects/.../memory/`) and project settings:
   ```
   rsync -av ~/.claude/ <new-box>:~/.claude/
   ```
3. **`~/.ssh` and `~/.gitconfig` move separately** — never bundle them under
   `~/.claude` (they're credentials/identity, not agent state; keep the blast
   radius of any single copy operation small):
   ```
   rsync -av ~/.ssh/ <new-box>:~/.ssh/
   scp ~/.gitconfig <new-box>:~/.gitconfig
   ```
4. **nix is assumed preinstalled** on the new box (owner standard, 2026-07-18
   decision) — bootstrap.sh and the cargo/rustup path don't require it, but
   `flake.nix` (Phase 3 step 1) does.

## Phase 3 — on arrival, in order

1. **Enter the pinned toolchain:**
   ```
   nix develop
   ```
   First run resolves `flake.nix`'s pinned nixpkgs input and generates
   `flake.lock` — **commit it** (`git add flake.lock && git commit`) so every
   later `nix develop` anywhere is fully hermetic. (This step cannot be verified
   on the box this checklist was authored on — no nix installed there; see
   `flake.nix`'s header for the nixpkgs pin this generates against.)
2. **Fetch the git-ignored assets** (reference jar + corpora):
   ```
   scripts/bootstrap.sh
   ```
3. **Run the full workspace gauntlet:**
   ```
   cargo build --workspace --all-targets && \
   cargo fmt --all --check && \
   cargo clippy --all-targets --all-features -- -D warnings && \
   cargo test --workspace
   ```
   The 5 jar-integration tests in `crates/als-conform/tests/oracle_integration.rs`
   pin the known 87/1129 enumeration facts (symmetry=20 vs symmetry=0 exhaustive
   counts on `oracle/test1.als`'s `show` command) — a wrong jar version or a wrong
   JDK fails these immediately, before anything more expensive runs.

   **Toolchain caveat:** inside `nix develop` the compiler is nixpkgs' rustc
   (1.95.0 at the current pin — see `flake.nix`'s header), NOT the 1.97.0 that
   `rust-toolchain.toml` pins and that every recorded gate ran at. If the
   gauntlet (esp. `fmt --check`/clippy) or step 4's hash diverges under the nix
   shell, suspect the toolchain delta FIRST: install the exact pin via rustup
   (`rustup toolchain install 1.97.0` — `cargo` then auto-selects it from
   `rust-toolchain.toml`) and re-run outside the nix shell before treating the
   divergence as real.
4. **Determinism cross-check.** Re-run the exact stage-1 sweep recorded in
   Phase 1 and compare stdout by hash — a byte-identical sweep across two
   different machines is mettle's determinism contract (STYLE.md: fixed solver
   build → byte-identical output), not a nuisance to wave away on mismatch:
   ```
   cargo build --release -p als-conform
   ./target/release/solve-gauge --jobs N | sha256sum
   ```
   Compare against the hash recorded in Phase 1. **Match:** the new box is a
   verified drop-in. **Mismatch:** stop the line — do not proceed to mt-050 or
   any deeper sweep until the divergence is root-caused (candidates: different
   rustc codegen affecting float-free-but-still-order-sensitive iteration,
   corpus drift, an uncommitted change on the old box that never made it into
   the recorded hash).
5. **Re-run the SB-0 counting net from the cached baselines:**
   ```
   ./target/release/solve-gauge --count
   ```
   Expect **count_match 49 / COUNT_MISMATCH 3** (verified post-mt-053, 2026-07-22; the three filed mt-041 rows —
   see `docs/TASKS.md`). Any other number is a new finding, not a known
   quantity — investigate before treating the box as ready for mt-050's
   deep-budget exit sweeps.

---

## See also
- [SESSION_WRAP.md](SESSION_WRAP.md) — what gets the old box into the state Phase 1 assumes.
- [reference/alloy6-reference.md](reference/alloy6-reference.md) — the jar pin `scripts/bootstrap.sh` fetches and SHA-256-verifies.
- [reference/corpora.md](reference/corpora.md) — the corpora pin `scripts/fetch-corpora.sh` (invoked by `bootstrap.sh`) fetches.
- `flake.nix` / `rust-toolchain.toml` (repo root) — the pinned toolchain Phase 3 step 1 enters.

---

## As executed — 2026-07-24, exe.dev VM (x86_64-linux) → MacBook Pro (aarch64-darwin)

**Outcome: verified drop-in.** The stage-1 sweep reproduced the recorded hash
`72ad3b33…` **byte-for-byte across architectures** (the first cross-arch test of
the determinism contract — 10-core M-series, macOS 26, rustc 1.97.0 via rustup
inside `nix develop`'s JDK 21 shell); full gauntlet 50 suites green incl. the 5
jar-integration facts; cached SB-0 net bucket-identical (49 / mt-041 ×3).

Deltas from the checklist as written, for the next migration:
- **Different path is fine** — the agent-memory directory was *re-keyed*, not
  same-path'd: copy `~/.claude/projects/<old-path-key>/memory/` to the new
  machine under the new path's key (`-Users-choong-repos-chaychoong-mettle`)
  and update absolute paths inside the memory files. Do NOT rsync `~/.claude`
  wholesale onto a machine that already uses Claude — merge only the project dir.
- **macOS notes:** `nix` may not be on non-interactive SSH `PATH` — invoke
  `/nix/var/nix/profiles/default/bin/nix` absolutely; `--extra-experimental-features
  "nix-command flakes"` needed unless the host config enables them. macOS
  `/bin/bash` is 3.2 — one `set -u` empty-array expansion bug in bootstrap.sh
  was found and fixed (`99444be`). This macOS ships `sha256sum` and `timeout`;
  older ones may not.
- **Two first-party fixture files lived in git-ignored `oracle/`** and were
  missing on the clean clone (the mt-006 lesson, fixture edition) — moved into
  `crates/als-conform/fixtures/` (`26ccd1d`). `oracle/` now holds only the jar.
- `flake.lock` generated on first `nix develop` and committed (`d997803`);
  the flake worked first try on `aarch64-darwin` (rustc 1.95.0 + OpenJDK 21.0.11;
  the 1.95-vs-1.97 caveat above stands — builds/tests ran at rustup's 1.97).
