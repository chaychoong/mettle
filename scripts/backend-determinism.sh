#!/usr/bin/env bash
# Cross-target determinism battery for the SAT backends (ADR-0019 / mt-089).
#
# Solves a small fixed suite with EVERY backend the given binary was built with
# and prints one `<solver> <model> <sha256-of-stdout>` line per (solver, model),
# in a fixed order. The output is the whole point: run it on several machines /
# release targets and diff the files.
#
#   ./scripts/backend-determinism.sh [path-to-mettle-binary]
#
# A `cadical` row differing across targets is a MEASUREMENT, not a bug —
# ADR-0019 §1 never promised cross-platform byte-identity for it, since its
# determinism is by pinning rather than by construction. Whether the answers
# survive the trip is exactly what we do not yet know, which is why this script
# exists and why `.cargo/config.toml` pins `-ffp-contract=off` first.
#
# Until mt-124 the report also carried `mettle` rows, the own CDCL, whose
# byte-identity across targets WAS a contract (STYLE D1) and served as the
# control. ADR-0027 decision 3 deleted that solver; the loop below reads the
# names out of the binary, so the report simply lost a column.
#
# Verdicts are a separate matter: a verdict is a property of the encoding, so a
# verdict difference is always a bug — but this script hashes whole instances,
# which are legitimately the backend's own. `backend-instrument --certify` is
# the tool that audits verdicts.
set -euo pipefail

BIN="${1:-./target/release/mettle}"
SUITE_DIR="$(cd "$(dirname "$0")/.." && pwd)/crates/mettle/tests/fixtures/determinism"

if [ ! -x "$BIN" ]; then
  echo "backend-determinism: no executable at $BIN" >&2
  exit 2
fi
if [ ! -d "$SUITE_DIR" ]; then
  echo "backend-determinism: no suite at $SUITE_DIR" >&2
  exit 2
fi

# sha256sum on Linux, shasum on macOS; both print "<hash>  <file>".
sha256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | cut -d' ' -f1
  else
    shasum -a 256 | cut -d' ' -f1
  fi
}

# The solver names this binary actually has, read out of its own help text
# rather than hardcoded — a build offering fewer backends must produce a shorter
# (still comparable) report, not a failure.
solvers() {
  # `head -1` because the usage text lists the flag once per subcommand that
  # takes it (exec and serve), with the same names both times.
  "$BIN" exec --help 2>&1 |
    sed -n 's/^  --solver <name>        SAT backend, one of: \(.*\) (default:.*/\1/p' |
    head -1 |
    tr -d ','
}

echo "# mettle backend determinism battery"
echo "# binary: $("$BIN" -V)"
echo "# target: ${TARGET:-unknown}"
for solver in $(solvers); do
  for model in "$SUITE_DIR"/*.als; do
    # `exec` exits non-zero on an `expect` mismatch or a non-verdict; the run is
    # still a measurement, so the status is deliberately ignored and only stdout
    # (the verdicts and instances) is hashed. stderr carries absolute paths and
    # is excluded for that reason.
    hash=$("$BIN" exec "$model" --solver "$solver" 2>/dev/null | sha256 || true)
    echo "$solver $(basename "$model") $hash"
  done
done
