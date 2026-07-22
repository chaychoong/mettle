#!/usr/bin/env bash
#
# bootstrap.sh — one-command asset bootstrap for a fresh mettle clone.
#
# Fetches everything a fresh clone is missing because it's git-ignored:
#   1. the pinned reference Alloy jar into oracle/ (SHA-256 verified on
#      download; the pin is docs/reference/alloy6-reference.md)
#   2. the conformance corpora, by delegating to scripts/fetch-corpora.sh
#      (see that script / docs/reference/corpora.md for corpora provenance)
#
# Usage:
#   scripts/bootstrap.sh [--with-alloy4fun]
#   scripts/bootstrap.sh --verify
#
#   --with-alloy4fun   forwarded to fetch-corpora.sh: also fetch the 374 MB
#                       alloy4fun Zenodo dataset (skipped by default)
#   --verify            don't fetch anything; check the jar's SHA-256 and
#                       delegate corpus checking to fetch-corpora.sh --verify
#
# The jar step is idempotent and safe: if oracle/org.alloytools.alloy.dist.jar
# already exists and its SHA-256 matches the pin, nothing is downloaded. If
# it exists and mismatches, bootstrap.sh refuses (nonzero exit) and does NOT
# overwrite the file — a corrupt or unexpected jar is the user's call, not
# something to silently paper over.
#
# Dependencies: bash, curl, coreutils (sha256sum). Everything fetch-corpora.sh
# needs (git, tar, python3) is needed transitively for the corpora step.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
FETCH_CORPORA="${SCRIPT_DIR}/fetch-corpora.sh"

# --- pins (see docs/reference/alloy6-reference.md for the full provenance record) ---
JAR_URL="https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar"
JAR_SHA256="6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d"
JAR_DIR="${REPO_ROOT}/oracle"
JAR_PATH="${JAR_DIR}/org.alloytools.alloy.dist.jar"

WITH_ALLOY4FUN=0
VERIFY=0

usage() {
  sed -n '2,20p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --with-alloy4fun) WITH_ALLOY4FUN=1; shift ;;
    --verify) VERIFY=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "bootstrap.sh: unknown argument: $1" >&2; usage; exit 1 ;;
  esac
done

log() { printf '[bootstrap] %s\n' "$*" >&2; }

jar_sha256() {
  sha256sum "$1" | cut -d' ' -f1
}

# A single staging root for the whole run, always cleaned on exit (success
# or failure) — same pattern as fetch-corpora.sh.
TMPROOT="$(mktemp -d "${TMPDIR:-/tmp}/bootstrap.XXXXXX")"
cleanup() { rm -rf "${TMPROOT}"; }
trap cleanup EXIT

# ---------------------------------------------------------------------------
# verify mode
# ---------------------------------------------------------------------------

verify_jar() {
  if [[ ! -f "$JAR_PATH" ]]; then
    echo "bootstrap.sh --verify: jar missing at ${JAR_PATH}" >&2
    return 1
  fi
  local actual
  actual="$(jar_sha256 "$JAR_PATH")"
  if [[ "$actual" != "$JAR_SHA256" ]]; then
    echo "bootstrap.sh --verify: jar SHA-256 mismatch" >&2
    echo "  expected: ${JAR_SHA256}" >&2
    echo "  actual:   ${actual}" >&2
    return 1
  fi
  echo "bootstrap.sh --verify: jar OK (${JAR_SHA256})"
  return 0
}

if [[ "$VERIFY" -eq 1 ]]; then
  jar_status=0
  verify_jar || jar_status=1

  corpora_status=0
  "$FETCH_CORPORA" --verify || corpora_status=1

  if [[ "$jar_status" -ne 0 || "$corpora_status" -ne 0 ]]; then
    echo "" >&2
    echo "bootstrap.sh --verify: FAIL" >&2
    exit 1
  fi
  echo ""
  echo "bootstrap.sh --verify: PASS"
  exit 0
fi

# ---------------------------------------------------------------------------
# jar fetch (idempotent, SHA-verified, never silently overwrites)
# ---------------------------------------------------------------------------

fetch_jar() {
  mkdir -p "$JAR_DIR"

  if [[ -f "$JAR_PATH" ]]; then
    local existing
    existing="$(jar_sha256 "$JAR_PATH")"
    if [[ "$existing" == "$JAR_SHA256" ]]; then
      log "jar: already present and SHA-256-verified at ${JAR_PATH}, skipping download."
      return 0
    fi
    echo "bootstrap.sh: ${JAR_PATH} already exists but its SHA-256 does not match the pin." >&2
    echo "  expected: ${JAR_SHA256}" >&2
    echo "  actual:   ${existing}" >&2
    echo "Refusing to overwrite. Move or remove the file yourself if you want it re-fetched," >&2
    echo "then re-run scripts/bootstrap.sh." >&2
    exit 1
  fi

  local tmpfile="${TMPROOT}/org.alloytools.alloy.dist.jar"

  log "jar: downloading from ${JAR_URL}..."
  curl -sSfL -o "$tmpfile" "$JAR_URL"

  local actual
  actual="$(jar_sha256 "$tmpfile")"
  if [[ "$actual" != "$JAR_SHA256" ]]; then
    echo "bootstrap.sh: downloaded jar failed SHA-256 verification." >&2
    echo "  expected: ${JAR_SHA256}" >&2
    echo "  actual:   ${actual}" >&2
    echo "Not installing it. This means either the download was corrupted (re-run to retry)" >&2
    echo "or the upstream release asset / the pin in docs/reference/alloy6-reference.md has drifted" >&2
    echo "(needs investigation, not a blind re-pin)." >&2
    exit 1
  fi

  mv "$tmpfile" "$JAR_PATH"
  log "jar: verified and installed at ${JAR_PATH} (${JAR_SHA256})."
}

fetch_jar

# ---------------------------------------------------------------------------
# corpora fetch (delegated)
# ---------------------------------------------------------------------------

corpora_args=()
[[ "$WITH_ALLOY4FUN" -eq 1 ]] && corpora_args+=(--with-alloy4fun)

log "corpora: delegating to fetch-corpora.sh ${corpora_args[*]:-}..."
"$FETCH_CORPORA" "${corpora_args[@]}"

# ---------------------------------------------------------------------------
# next steps
# ---------------------------------------------------------------------------

log "done."
cat >&2 <<EOF

Next steps:
  cargo build --workspace --all-targets
  cargo test -p als-conform --test oracle_integration
EOF
