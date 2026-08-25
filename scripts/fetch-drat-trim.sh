#!/usr/bin/env bash
#
# fetch-drat-trim.sh — build the DRAT proof checker the certification
# instrument verifies UNSAT verdicts with (ADR-0027 decision 4, mt-123).
#
#   scripts/fetch-drat-trim.sh [--force]
#
# Lands an executable at tools/drat-trim/drat-trim, which is where
# `backend-instrument --certify` looks by default. Idempotent: an existing
# binary is left alone unless --force.
#
# drat-trim is a dev-side tool, exactly like the reference jar and the
# conformance corpora: fetched by script at a pinned commit, git-ignored, and
# never a shipped dependency of mettle. A mettle build does not need it and a
# mettle user never runs it; only the gauge and CI do.
#
# Dependencies: bash, curl, tar, and a C compiler ($CC, default cc).

set -euo pipefail

# --- pin (recorded with its license in docs/adr/0027-cadical-only-solver.md) ---
# marijnheule/drat-trim, master as of 2026-08-25. MIT licensed; the LICENSE
# file is copied next to the binary so the tree carries its own attribution.
DRAT_TRIM_SHA="2e3b2dc0ecf938addbd779d42877b6ed69d9a985"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
DEST="${REPO_ROOT}/tools/drat-trim"
BINARY="${DEST}/drat-trim"

FORCE=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --force) FORCE=1; shift ;;
    -h|--help) sed -n '2,19p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "fetch-drat-trim.sh: unknown argument: $1" >&2; exit 1 ;;
  esac
done

log() { printf '[fetch-drat-trim] %s\n' "$*" >&2; }

if [[ -x "${BINARY}" && "${FORCE}" -ne 1 ]]; then
  log "already built at ${BINARY} (use --force to rebuild)."
  exit 0
fi

CC="${CC:-cc}"
if ! command -v "${CC}" >/dev/null 2>&1; then
  echo "fetch-drat-trim.sh: no C compiler found (tried '${CC}'); set CC to one" >&2
  exit 1
fi

# Staged in a temp dir and moved into place only once the build succeeds, so a
# failed run never leaves a half-populated tools/drat-trim behind.
STAGE="$(mktemp -d "${TMPDIR:-/tmp}/fetch-drat-trim.XXXXXX")"
trap 'rm -rf "${STAGE}"' EXIT

log "downloading marijnheule/drat-trim@${DRAT_TRIM_SHA}..."
curl -sSfL -o "${STAGE}/drat-trim.tar.gz" \
  "https://github.com/marijnheule/drat-trim/archive/${DRAT_TRIM_SHA}.tar.gz"
tar xzf "${STAGE}/drat-trim.tar.gz" -C "${STAGE}"
SRC="${STAGE}/drat-trim-${DRAT_TRIM_SHA}"

# Compiled directly rather than through upstream's Makefile: that Makefile
# hard-codes `gcc` (absent on a stock macOS) and also builds four companion
# tools — lrat-check, compress, decompress, gapless — that nothing here uses.
# The flags are its own drat-trim recipe, verbatim.
log "compiling with ${CC}..."
(cd "${SRC}" && "${CC}" drat-trim.c -std=c99 -O2 -o drat-trim)

mkdir -p "${DEST}"
mv "${SRC}/drat-trim" "${BINARY}"
cp "${SRC}/LICENSE" "${DEST}/LICENSE"
cat > "${DEST}/PROVENANCE.txt" <<EOF
drat-trim — DRAT proof checker
Source:  https://github.com/marijnheule/drat-trim
Commit:  ${DRAT_TRIM_SHA}
License: MIT (see LICENSE next to this file)
Authors: Marijn Heule, Nathan Wetzler (The University of Texas at Austin)

Fetched and built by scripts/fetch-drat-trim.sh. Dev-side only: never
committed, never shipped, never linked into mettle. Used by
\`backend-instrument --certify\` to check the DRAT proofs CaDiCaL logs for
UNSAT verdicts (ADR-0027 decision 4, mt-123).
EOF

log "built ${BINARY}."
"${BINARY}" 2>&1 | head -3 || true
