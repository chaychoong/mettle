#!/usr/bin/env bash
# watch-status.sh — observe a long solve-gauge / refresh-counts run (mt-054 (d)).
#
# Exists for the product owner to watch a long sweep without tailing stderr: the
# StatusFile writes a single plain-text file (tool + args, phase, k/N progress,
# current file, elapsed, last ~10 heartbeats, and a final DONE line) that this
# script re-displays every 2 seconds.
#
# Usage:
#   scripts/watch-status.sh                 # watch status/solve-gauge.txt
#   scripts/watch-status.sh refresh-counts  # watch status/refresh-counts.txt
#   scripts/watch-status.sh path/to/file    # watch an explicit --status-file path
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
arg="${1:-solve-gauge}"

case "$arg" in
  */*|*.txt) target="$arg" ;;                       # explicit path
  *)         target="$root/status/$arg.txt" ;;      # a tool name
esac

echo "watching: $target"
if command -v watch >/dev/null 2>&1; then
  exec watch -n2 cat "$target"
else
  # Fallback when `watch` is unavailable: follow the file (it is atomically
  # rewritten, so re-cat on an interval keeps it readable).
  while true; do
    clear 2>/dev/null || true
    cat "$target" 2>/dev/null || echo "(no status file yet at $target)"
    sleep 2
  done
fi
