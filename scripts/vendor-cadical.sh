#!/usr/bin/env bash
# Regenerates vendor/cadical from the pristine crates.io copy of `cadical`
# 0.1.16 plus vendor/cadical-mettle.patch (ADR-0027 / mt-121). See
# vendor/README.md for what the patch adds and why the fork exists.
#
#   ./scripts/vendor-cadical.sh
#
# The pristine source is cargo's own registry checkout, so the crate must have
# been downloaded once (any `cargo fetch` of a tree that depends on it does
# that). Nothing here reaches the network.
#
# Regenerating and getting a dirty `vendor/cadical` back means the patch and the
# vendored tree have drifted apart; re-derive the patch instead of hand-editing
# both:
#
#   diff the pristine copy (cleaned exactly as below) against vendor/cadical
#   with `git diff --no-index --no-prefix`, and write it to
#   vendor/cadical-mettle.patch.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
src=$(ls -d "$HOME"/.cargo/registry/src/*/cadical-0.1.16 2>/dev/null | head -1)
if [ -z "${src:-}" ] || [ ! -d "$src" ]; then
  echo "vendor-cadical: no cadical-0.1.16 in the cargo registry; run 'cargo fetch' first" >&2
  exit 2
fi

rm -rf "$root/vendor/cadical"
mkdir -p "$root/vendor"
cp -R "$src" "$root/vendor/cadical"
# Registry checkouts are read-only and carry three files that are cargo's
# bookkeeping rather than the crate: the download marker, a lockfile a path
# dependency never uses, and the pre-normalization manifest.
chmod -R u+w "$root/vendor/cadical"
rm -f "$root/vendor/cadical/.cargo-ok" \
  "$root/vendor/cadical/Cargo.lock" \
  "$root/vendor/cadical/Cargo.toml.orig"

patch -d "$root/vendor/cadical" -p1 --no-backup-if-mismatch < "$root/vendor/cadical-mettle.patch"
echo "vendor-cadical: regenerated $root/vendor/cadical from $src"
