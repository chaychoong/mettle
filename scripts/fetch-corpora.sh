#!/usr/bin/env bash
#
# fetch-corpora.sh — reproducibly fetch mettle's conformance corpora.
#
# This script IMPLEMENTS acquisition; the authoritative PROVENANCE record
# (source pins, commit SHAs, Zenodo DOI, retrieval commands, filtering
# pipeline, gotchas, license evidence) is docs/reference/corpora.md — read
# that first. If the two ever disagree, the manifest is the design intent
# and this script has a bug.
#
# Usage:
#   scripts/fetch-corpora.sh [--with-alloy4fun] [--force]
#   scripts/fetch-corpora.sh --verify
#
#   --with-alloy4fun   also fetch the 374 MB alloy4fun Zenodo dataset
#                       (skipped by default; big and rarely needed)
#   --force             re-fetch a corpus even if its directory already
#                       exists under $CORPUS_DIR
#   --verify            don't fetch anything; check the existing corpus
#                       tree against scripts/corpora.sha256 and report
#                       pass/fail (a missing alloy4fun/ dir is "skipped",
#                       not a failure, since it's optional)
#
# Env:
#   CORPUS_DIR          where corpora land (default: corpus/, relative to
#                       the repo root this script lives under)
#
# Dependencies: bash, curl, git, tar, python3, coreutils (sha256sum). No
# exotic tooling. The WatForm/portus-evaluation shell/python scripts that
# document the portus-63 filtering pipeline are fetched (as data, at a
# pinned commit) and their *documented logic* is reimplemented here in
# inline python3 — they are never executed.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
CORPUS_DIR="${CORPUS_DIR:-${REPO_ROOT}/corpus}"
CHECKSUM_FILE="${SCRIPT_DIR}/corpora.sha256"

# --- pins (see docs/reference/corpora.md for the full provenance record) ---
ALLOYTOOLS_SHA="794226dd07b536fe35c5ca44b529417183cd629b"
ZENODO_RECORD="17390557"
# WatForm/portus-evaluation: manifest documents the *content* pins (10 repos
# + 1 file, each below) but the two list/script files (keep-list and
# unsupported-list) are sourced from this aggregator repo. No commit was
# pinned for it in the manifest at authoring time, so this script pins the
# commit that was HEAD of main on the manifest's retrieval date (2026-07-15)
# and records it here as the reproducibility pin for those two files.
PORTUS_EVAL_SHA="553296a97d5ac087f44a5563bb3bcb90db519d6c"

PAMELAZAVE_UA="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36"

WITH_ALLOY4FUN=0
FORCE=0
VERIFY=0

usage() {
  sed -n '2,30p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --with-alloy4fun) WITH_ALLOY4FUN=1; shift ;;
    --force) FORCE=1; shift ;;
    --verify) VERIFY=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "fetch-corpora.sh: unknown argument: $1" >&2; usage; exit 1 ;;
  esac
done

log() { printf '[fetch-corpora] %s\n' "$*" >&2; }

# A single staging root for the whole run; always cleaned on exit (success
# or failure). Successfully-fetched corpora are moved OUT of it into
# CORPUS_DIR before that happens, so a clean exit leaves nothing behind
# either way — "clean up staging on failure" and "don't leave temp cruft on
# success" fall out of the same trap.
TMPROOT="$(mktemp -d "${TMPDIR:-/tmp}/fetch-corpora.XXXXXX")"
cleanup() { rm -rf "${TMPROOT}"; }
trap cleanup EXIT

# ---------------------------------------------------------------------------
# verify mode
# ---------------------------------------------------------------------------

verify() {
  if [[ ! -f "${CHECKSUM_FILE}" ]]; then
    echo "fetch-corpora.sh --verify: no checksum manifest at ${CHECKSUM_FILE}" >&2
    exit 1
  fi

  local alloy4fun_present=1
  [[ -d "${CORPUS_DIR}/alloy4fun" ]] || alloy4fun_present=0

  local checked=0 skipped=0 missing=0 mismatched=0
  local -a bad_lines=()

  while IFS= read -r line; do
    [[ -z "$line" ]] && continue
    local expected_hash rel_path
    expected_hash="${line%%  *}"
    rel_path="${line#*  }"

    if [[ "$rel_path" == alloy4fun/* && "$alloy4fun_present" -eq 0 ]]; then
      skipped=$((skipped + 1))
      continue
    fi

    local full_path="${CORPUS_DIR}/${rel_path}"
    if [[ ! -f "$full_path" ]]; then
      missing=$((missing + 1))
      bad_lines+=("MISSING   ${rel_path}")
      continue
    fi

    local actual_hash
    actual_hash="$(sha256sum "$full_path" | cut -d' ' -f1)"
    checked=$((checked + 1))
    if [[ "$actual_hash" != "$expected_hash" ]]; then
      mismatched=$((mismatched + 1))
      bad_lines+=("MISMATCH  ${rel_path}")
    fi
  done < "${CHECKSUM_FILE}"

  echo "fetch-corpora.sh --verify:"
  echo "  checked:   ${checked}"
  echo "  skipped:   ${skipped} (alloy4fun/ absent — optional corpus, not fetched)"
  echo "  missing:   ${missing}"
  echo "  mismatched:${mismatched}"

  if [[ "${#bad_lines[@]}" -gt 0 ]]; then
    echo ""
    echo "diff of mismatches:"
    printf '  %s\n' "${bad_lines[@]}"
    echo ""
    echo "FAIL"
    exit 1
  fi

  echo ""
  echo "PASS"
}

if [[ "$VERIFY" -eq 1 ]]; then
  verify
  exit 0
fi

# ---------------------------------------------------------------------------
# alloytools-models
# ---------------------------------------------------------------------------

fetch_alloytools_models() {
  local stage="${TMPROOT}/alloytools-models"
  mkdir -p "$stage"
  local prefix="org.alloytools.alloy-${ALLOYTOOLS_SHA}"

  log "alloytools-models: downloading org.alloytools.alloy@${ALLOYTOOLS_SHA}..."
  curl -sSfL -o "${stage}/alloy.tar.gz" \
    "https://github.com/AlloyTools/org.alloytools.alloy/archive/${ALLOYTOOLS_SHA}.tar.gz"

  (
    cd "$stage"
    tar xzf alloy.tar.gz \
      "${prefix}/org.alloytools.alloy.core/src/main/resources/models/" \
      "${prefix}/org.alloytools.alloy.extra/extra/models/" \
      "${prefix}/LICENSE" \
      "${prefix}/README.md"
  )

  # Flatten the two-module split into one models/ root, matching the
  # jar's own packaged layout (see docs/reference/corpora.md §1).
  mkdir -p "${stage}/models"
  mv "${stage}/${prefix}/org.alloytools.alloy.core/src/main/resources/models/util" \
     "${stage}/models/util"
  mv "${stage}/${prefix}/org.alloytools.alloy.extra/extra/models/book" \
     "${stage}/models/book"
  mv "${stage}/${prefix}/org.alloytools.alloy.extra/extra/models/examples" \
     "${stage}/models/examples"
  mv "${stage}/${prefix}/LICENSE" "${stage}/LICENSE"
  mv "${stage}/${prefix}/README.md" "${stage}/README.md"

  # Pruning: keep only .als, LICENSE, README.md — drop the .thm
  # (Sterling/visualizer theme) files that ride along with book/examples.
  find "${stage}/models" -name '*.thm' -delete

  rm -rf "${stage:?}/${prefix:?}" "${stage:?}/alloy.tar.gz"

  log "alloytools-models: done ($(find "$stage" -type f | wc -l) files)."
  echo "$stage"
}

# ---------------------------------------------------------------------------
# portus-63
# ---------------------------------------------------------------------------

# download <repo-url> <commit-sha> <dest-dir-relative-to-cwd>
# Mirrors the download() helper documented verbatim in
# docs/reference/corpora.md / WatForm/portus-evaluation's
# get-expert-models.sh, plain git protocol (no GitHub API, no rate limits).
# The resulting .git/ is stripped once checked out — it's not part of the
# vendored corpus and every downstream filtering step operates on file
# content only.
clone_pinned() {
  local repo="$1" commit="$2" dir="$3"
  mkdir -p "$dir"
  (
    cd "$dir"
    git init -q
    git remote add origin "$repo"
    git fetch -q origin "$commit"
    git reset -q --hard FETCH_HEAD
  )
  rm -rf "${dir}/.git"
}

# filter_portus63 <stage-dir> <needed-names-file> <remove-unsupported.py>
#
# Reimplements (never executes) the pipeline documented in
# docs/reference/corpora.md §3 / WatForm/portus-evaluation's
# setup_scripts/{remove-unneeded-files,fix-models,remove-unsupported,
# compile-top-level-file-list}.{sh,py}, run over <stage-dir>/expert-models/:
#
#   1. keep-list filter   — keep only files named in the keep-list (first
#      field of each comma-separated line = top-level model; rest = its
#      open-imported dependencies), drop everything else, prune empty dirs.
#   2. Alloy-6 syntax fix — global ' -> " over every .als file, then append
#      " after every occurrence (blind substring match, same bluntness as
#      the original sed) of each of the 15 now-reserved keywords; plus 4
#      model-specific patches: dbs_inst.als "open DBS"->"open dbs" casing,
#      trace.als "predtotalOrder"->"pred/totalOrder" typo, tso_transistency_*
#      bare "for N" -> "for N but 5 Int" bitwidth bump, birthday.als
#      comment-out of the AddWorks/BusyDay assertions Portus doesn't support
#      (fixed line ranges 50-53, 61, 64-68, 1-indexed, post-syntax-fix).
#   3. unsupported removal — delete the 11 top-level models parsed out of
#      remove-unsupported.py's `rmfiles.append(Path("..."))` calls.
#   4. dependency pruning  — of the keep-list's 74 top-level entries, the
#      ones still on disk are "supported" (63 of them); drop any dependency
#      file no longer referenced by a surviving top-level model; write
#      models-supported.txt.
#
# Python text-mode I/O universal-newline-translates on read and emits '\n'
# on write on Linux — this is what normalizes the CRLF line endings some of
# the (old, Windows-authored) source repos carry to the LF-only files
# actually vendored in corpus/, with no separate handling needed here.
filter_portus63() {
  local stage="$1" needed_names_file="$2" remove_unsupported_file="$3"
  python3 - "$stage" "$needed_names_file" "$remove_unsupported_file" <<'PYEOF'
import re
import sys
from pathlib import Path

KEYWORDS = [
    "after", "always", "before", "enabled", "eventually", "historically",
    "invariant", "modifies", "once", "releases", "since", "steps",
    "triggered", "until", "var",
]

DBS_INST_FILES = [
    "expert-models/7z32luflamhdcixvt6nwznnud4oi6dbr-MSV/Systems/CD2DBS_keys/dbs_inst.als",
    "expert-models/7z32luflamhdcixvt6nwznnud4oi6dbr-MSV/Systems/CD2DBS_simple/dbs_inst.als",
]
TRACE_FILES = [
    "expert-models/7z32luflamhdcixvt6nwznnud4oi6dbr-MSV/Systems/ElevatorSPL/trace.als",
    "expert-models/gumxtrzzbkrtwi7jtwyu7eibi3fwhgmf-models/utilities/trace/trace.als",
]
TSO_BITWIDTH_FILES = [
    "expert-models/x7t75qqe5fr6uzitot5sdu63o7drnur5-TransForm/util/tso_transistency_perturbed_minimize.als",
    "expert-models/x7t75qqe5fr6uzitot5sdu63o7drnur5-TransForm/util/tso_transistency_perturbed_minimality_check.als",
]
BITWIDTH_RE = re.compile(r" for (\d+)")
BIRTHDAY_FILE = "expert-models/gumxtrzzbkrtwi7jtwyu7eibi3fwhgmf-models/simple-models/books/birthday.als"
BIRTHDAY_COMMENT_LINES = list(range(50, 54)) + [61] + list(range(64, 69))


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return path.read_text(encoding="latin-1")


def fix_syntax(text: str) -> str:
    text = text.replace("'", '"')
    for kw in KEYWORDS:
        text = text.replace(kw, kw + '"')
    return text


def remove_empty_dirs(base: Path) -> None:
    for p in sorted(base.rglob("*"), key=lambda x: len(x.parts), reverse=True):
        if p.is_dir() and not any(p.iterdir()):
            p.rmdir()


def main() -> None:
    stage = Path(sys.argv[1])
    needed_names_file = Path(sys.argv[2])
    remove_unsupported_file = Path(sys.argv[3])
    models_dir = stage / "expert-models"
    models_supported_file = stage / "models-supported.txt"

    top_level_order = []
    all_model_files = {}
    found_file = {}
    with open(needed_names_file, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip():
                continue
            fields = [f.strip() for f in line.split(",")]
            top_level = fields[0]
            top_level_order.append(top_level)
            for f in fields:
                found_file[f] = False
                all_model_files.setdefault(f, []).append(top_level)

    # step 1: keep-list filter
    for p in sorted(models_dir.rglob("*")):
        if not p.is_file():
            continue
        rel = str(p.relative_to(stage))
        if rel in found_file:
            found_file[rel] = True
        else:
            p.unlink()
    remove_empty_dirs(models_dir)

    missing = [k for k, v in found_file.items() if not v]
    if missing:
        print(f"warning: {len(missing)} keep-list files not found after download:", file=sys.stderr)
        for m in missing:
            print(f"  {m}", file=sys.stderr)

    # step 2: Alloy-6 syntax fixes
    als_files = sorted(models_dir.rglob("*.als"))
    for p in als_files:
        p.write_text(fix_syntax(read_text(p)), encoding="utf-8")

    for rel in DBS_INST_FILES:
        p = stage / rel
        if p.exists():
            p.write_text(read_text(p).replace("open DBS", "open dbs"), encoding="utf-8")

    for rel in TRACE_FILES:
        p = stage / rel
        if p.exists():
            p.write_text(read_text(p).replace("predtotalOrder", "pred/totalOrder"), encoding="utf-8")

    for rel in TSO_BITWIDTH_FILES:
        p = stage / rel
        if p.exists():
            p.write_text(BITWIDTH_RE.sub(r" for \1 but 5 Int", read_text(p)), encoding="utf-8")

    birthday = stage / BIRTHDAY_FILE
    if birthday.exists():
        lines = read_text(birthday).split("\n")
        for lineno in BIRTHDAY_COMMENT_LINES:
            idx = lineno - 1
            if 0 <= idx < len(lines):
                lines[idx] = "//" + lines[idx]
        birthday.write_text("\n".join(lines), encoding="utf-8")

    # step 3: unsupported removal (list parsed out of remove-unsupported.py, never executed)
    ru_text = remove_unsupported_file.read_text(encoding="utf-8")
    unsupported = re.findall(r'rmfiles\.append\(Path\("([^"]+)"\)\)', ru_text)
    if len(unsupported) != 11:
        print(
            f"error: expected 11 unsupported-model entries in remove-unsupported.py, "
            f"parsed {len(unsupported)}",
            file=sys.stderr,
        )
        sys.exit(1)
    for rel in unsupported:
        p = stage / rel
        if p.exists():
            p.unlink()

    # step 4: dependency pruning + models-supported.txt
    kept_top_level = {t: (stage / t).exists() for t in top_level_order}

    for p in sorted(models_dir.rglob("*")):
        if not p.is_file():
            continue
        rel = str(p.relative_to(stage))
        owners = all_model_files.get(rel)
        if owners is not None:
            if not any(kept_top_level.get(o, False) for o in owners):
                p.unlink()

    # Note: unlike step 1, the upstream compile-top-level-file-list.py does
    # NOT prune now-empty directories after this pass (it only os.remove()s
    # files) — so neither do we, to match the vendored tree exactly.

    with open(models_supported_file, "w", encoding="utf-8") as out:
        for t in top_level_order:
            if kept_top_level[t]:
                out.write(t + "\n")

    n_supported = sum(1 for v in kept_top_level.values() if v)
    n_als = sum(1 for _ in models_dir.rglob("*.als"))
    print(
        f"filter-portus63: {n_supported} top-level supported models, "
        f"{n_als} .als files on disk",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
PYEOF
}

fetch_portus63() {
  local stage="${TMPROOT}/portus-63"
  local models="${stage}/expert-models"
  mkdir -p "$models"

  log "portus-63: cloning 10 pinned source repos..."
  (
    cd "$models"
    clone_pinned https://github.com/ogiroux/talks.git                   a837092e73024383ab0e5bbace3f6b18ffbc655d  2scxlb3tbo5bmvmwplglqils7a5uarmx-talks
    clone_pinned https://github.com/atdyer/alloy.git                    09cbc14fc85bfea4f95351e4c921d091ecc8b94d  3zltn65gds66b6f4q3lvbtgdkb6snmuu-alloy
    clone_pinned https://github.com/pron/amazon-snapshot-spec.git       9c60cb18151889d7b4c0a4ffd7de0b6fc2db0fb2  7d25ioxqmue65lp6ntzz735gpbg4fmgq-amazon-snapshot-spec
    clone_pinned https://github.com/nmacedo/MSV.git                     6170c1473407d75ab2949ef6dcbb243b210d009c  7z32luflamhdcixvt6nwznnud4oi6dbr-MSV
    clone_pinned https://github.com/BGCX261/zigbee-alloy-svn-to-git.git 020bdb6a648a547e6bf1476533b602c4badaf82a  lkicptlz3eklrbu7ppmltlkebwrvzhdq-zigbee-alloy-svn-to-git
    clone_pinned https://github.com/hkhojasteh/CANBus.git               f6c7b8966de590cbb61176a919dbe49c02e733b0  oujlbmnutprdhddstyudppn7t35n43os-CANBus
    clone_pinned https://github.com/NVlabs/litmustestgen.git            580bd7434b7ca9206f0eccbdcffe6d212eeb0994  5x4l2fj5nfbq3cz2dumwdt57g3kig3rd-litmustestgen
    clone_pinned https://github.com/AlloyTools/models.git               969f5f809c33c5f70e10b2aae1c747f6a10eac86  gumxtrzzbkrtwi7jtwyu7eibi3fwhgmf-models
    clone_pinned https://github.com/nadeshr/weak_atomics.git            61ee841c8710cd6d2bea2041b49291a61f840b35  x7tjf3r7wnejcplj75s2o6im45kjodhs-weak_atomics
    clone_pinned https://github.com/naorinh/TransForm.git               ff5c052adbc8ad0b11f9652f4886925216242516  x7t75qqe5fr6uzitot5sdu63o7drnur5-TransForm
  )

  log "portus-63: downloading standalone chord-pamela-zave file..."
  mkdir -p "${models}/chord-pamela-zave"
  # pamelazave.com returns HTTP 406 without a browser-like User-Agent.
  curl -sSfL -A "$PAMELAZAVE_UA" \
    -o "${models}/chord-pamela-zave/correctChord.als" \
    "https://www.pamelazave.com/correctChord.als"

  log "portus-63: fetching keep-list + unsupported-list from WatForm/portus-evaluation@${PORTUS_EVAL_SHA}..."
  curl -sSfL -o "${stage}/filenames-of-all-parts-of-expert-models.txt" \
    "https://raw.githubusercontent.com/WatForm/portus-evaluation/${PORTUS_EVAL_SHA}/setup_scripts/filenames-of-all-parts-of-expert-models.txt"
  curl -sSfL -o "${stage}/remove-unsupported.py" \
    "https://raw.githubusercontent.com/WatForm/portus-evaluation/${PORTUS_EVAL_SHA}/setup_scripts/remove-unsupported.py"

  log "portus-63: applying filtering pipeline (keep-list -> Alloy-6 fixes -> drop unsupported -> drop unreferenced deps)..."
  filter_portus63 "$stage" \
    "${stage}/filenames-of-all-parts-of-expert-models.txt" \
    "${stage}/remove-unsupported.py"

  rm -f "${stage}/filenames-of-all-parts-of-expert-models.txt" "${stage}/remove-unsupported.py"

  log "portus-63: done ($(find "$stage" -name '*.als' | wc -l) .als files)."
  echo "$stage"
}

# ---------------------------------------------------------------------------
# alloy4fun
# ---------------------------------------------------------------------------

fetch_alloy4fun() {
  local stage="${TMPROOT}/alloy4fun/2024-25"
  mkdir -p "$stage"

  log "alloy4fun: querying Zenodo record ${ZENODO_RECORD} file list..."
  curl -sSf "https://zenodo.org/api/records/${ZENODO_RECORD}" | python3 -c "
import json, sys
d = json.load(sys.stdin)
for f in d['files']:
    print(f['key'], f['links']['self'])
" > "${stage}/alloy4fun_files.txt"

  local n
  n="$(wc -l < "${stage}/alloy4fun_files.txt")"
  log "alloy4fun: downloading ${n} files (~374 MB total)..."
  local i=0
  while read -r name url; do
    i=$((i + 1))
    log "alloy4fun: [${i}/${n}] ${name}"
    curl -sSfL -o "${stage}/${name}" "$url"
  done < "${stage}/alloy4fun_files.txt"
  rm -f "${stage}/alloy4fun_files.txt"

  cat > "${stage}/PROVENANCE.txt" <<'EOF'
Alloy4Fun Dataset for 2024/25
DOI: 10.5281/zenodo.17390557
Publication date: 2025-10 (Zenodo metadata `publication_date`)
License (Zenodo metadata `license.id`): cc-by-4.0 (Creative Commons Attribution 4.0 International)
Creators: Nuno Macedo (FEUP & INESC TEC), Alcino Cunha (UM & INESC TEC), Ana C. R. Paiva (FEUP & INESC TEC)
Source: https://zenodo.org/records/17390557

No bundled LICENSE/README file ships inside the Zenodo file set itself (it is
21 raw .json data files); this note transcribes the license/citation metadata
recorded by the Zenodo API (`GET /api/records/17390557`), quoted verbatim in
docs/reference/corpora.md. Retrieved 2026-07-15.
EOF

  log "alloy4fun: done ($(find "${TMPROOT}/alloy4fun" -type f | wc -l) files)."
  echo "${TMPROOT}/alloy4fun"
}

# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

mkdir -p "$CORPUS_DIR"

want=(alloytools-models portus-63)
[[ "$WITH_ALLOY4FUN" -eq 1 ]] && want+=(alloy4fun)

for name in "${want[@]}"; do
  target="${CORPUS_DIR}/${name}"
  if [[ -d "$target" && "$FORCE" -ne 1 ]]; then
    log "${name}: already exists at ${target}, skipping (use --force to re-fetch)."
    continue
  fi

  case "$name" in
    alloytools-models) staged="$(fetch_alloytools_models)" ;;
    portus-63) staged="$(fetch_portus63)" ;;
    alloy4fun) staged="$(fetch_alloy4fun)" ;;
    *) echo "fetch-corpora.sh: internal error: unknown corpus '$name'" >&2; exit 1 ;;
  esac

  rm -rf "$target"
  mv "$staged" "$target"
  log "${name}: installed at ${target}."
done

log "done."
