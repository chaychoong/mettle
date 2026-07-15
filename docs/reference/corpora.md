# Conformance corpora — provenance manifest

This document records how mettle's conformance corpora (mt-007) were
obtained, so acquisition is fully reproducible and mt-008 (mettle's own
licensing posture) has all the facts it needs to decide what, if anything,
mettle can eventually redistribute.

**Gate:** mettle's licensing posture is unresolved (mt-008). Per
[ADR-0002](../adr/0002-conformance-oracle.md), corpora are consumed locally by
the conformance harness (Net 0 `expect`-mining, verdict/count comparison
against the pinned oracle) but **are not committed to git**. `/corpus/` is
listed in `.gitignore`. Everything under `corpus/` is reproducible from the
commands recorded below — re-run them to regenerate the tree from scratch on
any machine.

This manifest follows the same evidence-based style as
[alloy6-reference.md §2](alloy6-reference.md): licenses are *recorded*, not
*adjudicated*. Nothing here is a legal conclusion; it's the raw material for
whoever resolves mt-008.

All retrieval below was performed **2026-07-15** from this VM (confirmed
outbound access to GitHub, Zenodo, and one third-party research-lab domain).

---

## 1. `alloytools-models`

The `.als` models bundled with the pinned Alloy 6.2.0 reference jar
([alloy6-reference.md](alloy6-reference.md)), fetched from source at the exact
commit the jar's own `MANIFEST.MF` (`Git-SHA`) says it was built from — so
this corpus is guaranteed to match the oracle's bundled standard library and
tutorial examples byte-for-byte (module names, no drift).

| | |
|---|---|
| Source | `AlloyTools/org.alloytools.alloy` on GitHub |
| Pin | commit `794226dd07b536fe35c5ca44b529417183cd629b` ("back to 6.2", 2024-07-09) — same commit as the jar's embedded `Git-SHA`, per alloy6-reference.md |
| Download date | 2026-07-15 |

**Retrieval (verbatim):**
```
curl -sL -o alloy.tar.gz \
  https://github.com/AlloyTools/org.alloytools.alloy/archive/794226dd07b536fe35c5ca44b529417183cd629b.tar.gz

PREFIX=org.alloytools.alloy-794226dd07b536fe35c5ca44b529417183cd629b
tar xzf alloy.tar.gz "${PREFIX}/org.alloytools.alloy.core/src/main/resources/models/"
tar xzf alloy.tar.gz "${PREFIX}/org.alloytools.alloy.extra/extra/models/"
tar xzf alloy.tar.gz "${PREFIX}/LICENSE" "${PREFIX}/README.md"
```

**Note on directory layout — deviates from the task brief.** At this commit
the `.als` files are **not** all under one directory
(`org.alloytools.alloy.core/src/main/resources/models/`) as originally
assumed. They are split across two Gradle modules in the source tree:
- `org.alloytools.alloy.core/src/main/resources/models/util/` — the 11
  standard-library files (`boolean.als`, `graph.als`, `integer.als`,
  `natural.als`, `ordering.als`, `relation.als`, `seqrel.als`, `sequence.als`,
  `sequniv.als`, `ternary.als`, `time.als`).
- `org.alloytools.alloy.extra/extra/models/{book,examples}/` — the 83
  book-appendix, book-chapter, and tutorial/example files.

At build/packaging time these get merged into the single `models/` resource
path inside the shipped jar (which is why alloy6-reference.md correctly
describes "94 `.als` files total bundled under `models/`" as a jar-level
fact); at the source-repo level, for this commit, they live in two places.
Vendored tree preserves this as `corpus/alloytools-models/models/{util,book,
examples}/` (flattened to one `models/` root, matching the jar's own layout,
rather than mirroring the two-module split).

**Pruning:** kept only `.als`, `LICENSE`, `README.md`. Removed 16 `.thm`
(Sterling/visualizer theme) files that came along with the `book`/`examples`
directories — not Alloy source, not license/readme.

| Metric | Value |
|---|---|
| Total size | 532 KB |
| `.als` file count | 94 (11 `util` + 83 `book`+`examples`) |
| Total files | 96 (94 `.als` + `LICENSE` + `README.md`) |
| `expect 0`/`expect 1` occurrences | 101 (`grep -rEoh 'expect[[:space:]]+[01]' --include='*.als' . \| wc -l`) |
| Files with ≥1 `expect` | 24 (`grep -rlE 'expect[[:space:]]+[01]' --include='*.als' . \| wc -l`) |
| Encoding | all files ASCII/UTF-8, `file` reports nothing non-text |
| Files using temporal keywords (`always`/`eventually`/`until`/`releases`/`historically`/`once`) | 12 — genuinely Alloy-6 (var/temporal) models, not stale Alloy-5 syntax |
| Files with `open util/...` | 39 |

**License evidence** (identical facts already established in
[alloy6-reference.md §2](alloy6-reference.md#2-licenses), re-verified against
this checkout — not repeated in full here, see that section for the complete
analysis):
- Repo root `LICENSE` (fetched at this commit) still opens with `# THIS IS
  NOT VALID YET! CURRENTLY CODE IS UNDER MIT LICENSE` followed by the
  Apache-2.0 license text — upstream's own admission of an unresolved
  MIT→Apache-2.0 relicensing-in-progress.
- Sample `.als` file headers (`models/book/appendixA/addressBook1.als`,
  `models/util/ordering.als`) carry **no per-file license/copyright header**
  — confirmed again at this exact commit, matching the reference doc's
  finding of "no separate per-file license/copyright header was found... for
  `util/*.als`", and the same holds for the `book`/`examples` files.
- No dedicated `NOTICE` entry exists for the `models/` tree.

---

## 2. `alloy4fun`

Student/novice Alloy models from the Alloy4Fun web platform (haslab /
INESC TEC, University of Minho + University of Porto formal-methods
courses), published as a dataset series on Zenodo. **Format is JSON Lines,
not bare `.als`** — see below. Per the task brief, no extractor was built;
the raw dataset is vendored as-is.

**Canonical source chosen:** the cumulative, most recent Zenodo record,
covering all course editions to date, rather than any single-year record.
Multiple yearly/edition-specific records also exist on Zenodo (concept DOI
groups them); e.g. `10.5281/zenodo.4665672` (2019/20, 9 files, 26.9 MB) and
`10.5281/zenodo.4676413` (2020/21) are earlier, smaller snapshots of the same
series. The 2024/25 record was chosen because its description states it
spans "fall 2019 through spring 2025" — i.e. it is the full cumulative
dataset, not an incremental one, making it the single most complete and
least redundant thing to vendor.

| | |
|---|---|
| Source | Zenodo record, haslab / Nuno Macedo, Alcino Cunha, Ana C. R. Paiva |
| Title | "Alloy4Fun Dataset for 2024/25" |
| Pin | DOI `10.5281/zenodo.17390557` |
| Publication date (Zenodo metadata) | 2025-10 |
| Download date | 2026-07-15 |

**Retrieval (verbatim):**
```
curl -s "https://zenodo.org/api/records/17390557" \
  | python3 -c "
import json,sys
d=json.load(sys.stdin)
for f in d['files']:
    print(f['key'], f['links']['self'])
" > alloy4fun_files.txt

while read -r name url; do
  curl -sL -o "$name" "$url"
done < alloy4fun_files.txt
```
(21 files downloaded, one `curl` per file to the Zenodo API's `/content`
endpoint for each recorded file key.)

**Format note (per task instructions — no extractor built, format
recorded as-is):** despite the `.json` extension, each file is **JSON
Lines** (one JSON object per line), not a single JSON array/object — a bare
`json.load()` on a whole file fails with "Extra data" after the first
record. Each line/record has keys: `_id`, `code`, `derivationOf`, `original`,
`theme`, `cmd_c`, `cmd_i`, `cmd_n`, `msg`, `sat`, `time`. The Alloy source
itself is the `code` field's string value (a full `.als`-equivalent module,
sometimes containing `//SECRET`-delimited instructor reference solutions
alongside the student's incomplete submission — an Alloy4Fun-specific
convention, not standard Alloy syntax). `sat` is a self-reported
verdict/status field from Alloy4Fun's own execution (`-1`/`0`/`1`/absent) —
potentially useful as a *second-order* cross-check signal later, but not
part of ADR-0002's Net 0 (which mines `expect` annotations from `.als`
source, not this platform-specific execution log) and not verified against
mettle's own solving here.

| Metric | Value |
|---|---|
| Total size | 374 MB (21 files, sizes verified byte-for-byte against the Zenodo API's reported file sizes) |
| Record count | 186,318 total JSON-Lines records across all 21 files (matches Zenodo's stated "~185,000 entries") |
| Records containing `expect 0`/`expect 1` in `code` | 59 records |
| Total `expect` occurrences (regex `expect\s+[01]` over all `code` fields) | 301 |
| `sat` field distribution | `1` (SAT): 75,368 · `0` (UNSAT): 54,484 · `-1` (error): 53,882 · absent (permalink only, not run): 2,584 |
| Encoding | all 21 files parse cleanly as UTF-8 |

**License evidence:**
- Zenodo record metadata (`GET /api/records/17390557` → `metadata.license.id`):
  **`cc-by-4.0`** (Creative Commons Attribution 4.0 International).
- Creators listed in Zenodo metadata: Nuno Macedo (FEUP & INESC TEC), Alcino
  Cunha (UM & INESC TEC), Ana C. R. Paiva (FEUP & INESC TEC).
- No LICENSE/README file ships inside the Zenodo file set itself (it is
  purely 21 `.json` data files) — the license is Zenodo *metadata*, not an
  in-repo file. Transcribed into
  `corpus/alloy4fun/2024-25/PROVENANCE.txt` for local reference since there's
  no bundled file to keep.
- Separately, the **Alloy4Fun webapp source** (`haslab/Alloy4Fun` on GitHub,
  not vendored here — only the dataset is) carries its own root `LICENSE`:
  `MIT License, Copyright (c) 2017 INESC TEC`. This governs the platform
  code, not the dataset content; noted for completeness since both are
  "Alloy4Fun" but are separately licensed artifacts.
- **Oddity:** the dataset's own README/description states "User comments
  were removed from the code to guarantee anonymization" — i.e. this is
  already a redacted/processed derivative of the raw student submissions,
  not the platform's raw database dump.

---

## 3. `portus-63`

The 63-model "Benchmark Set" of expert-written Alloy models used to evaluate
**Portus** ("Portus: Linking Alloy with SMT-based Finite Model Finding",
Dancy, Day, Zila, Tariq (U. Waterloo) + Poremba (UBC), arXiv:2411.15978).
**Correction to the task brief: this is a University of Waterloo / UBC
project, not KIT/Karlsruhe** — no Karlsruhe connection was found anywhere in
the paper, its authors, or its artifact repos; the task brief's guess about
the institution was wrong.

**Provenance chain (three hops, all public and independently verifiable):**
1. The Portus paper (§ Evaluation) states the corpus is a "Benchmark Set of
   models written by experts, scraped from the web by Eid and Day", citing
   Elias Eid & Nancy A. Day, *"Static Profiling of Alloy Models"*, IEEE TSE
   49(2):743–759, Feb 2023.
2. Portus's own evaluation-artifact repo, **`WatForm/portus-evaluation`**
   (GitHub, MIT license — confirmed via `GET /repos/WatForm/portus-evaluation`
   → `license.spdx_id: MIT`), documents and scripts the exact acquisition of
   this corpus from Eid & Day's original sources: `setup_scripts/
   get-expert-models.sh` (10 pinned `git` clones + 1 direct file download),
   `setup_scripts/filenames-of-all-parts-of-expert-models.txt` (Eid's
   original list of which files belong to which of 74 top-level models),
   `setup_scripts/fix-models.sh` (mechanical Alloy-5→6 syntax fixes: `'` →
   `"`, quote-suffix on now-reserved keywords, three model-specific patches),
   and `setup_scripts/remove-unsupported.py` (removes 11 of the 74 top-level
   models that Portus's engine can't handle, e.g. unsupported higher-order
   quantification) — **74 − 11 = 63**, exactly matching "the 63-model
   benchmark" named in the task brief. This is airtight: the number 63 is a
   direct, checked artifact of this pipeline, not a guess.
3. `README.md` in `portus-evaluation` names the pipeline's `make` target
   ("Setup - run `make` to set up the models... These models are the set of
   expert-models chosen for the paper: Elias Eid and Nancy A. Day. Static
   profiling Alloy models...").

**mettle did not execute the fetched `get-expert-models.sh` /
`remove-unneeded-files.py` / `remove-unsupported.py` scripts directly**
(sandboxed — running an unaudited third-party script was denied). Instead,
their documented logic was **read and reproduced by hand** (plain `git`
clone/fetch/reset commands issued directly, and small first-party Python
snippets replicating the two filtering scripts' documented behavior
exactly) — same end result, fully auditable, no blind script execution.

| | |
|---|---|
| Source (aggregator) | `WatForm/portus-evaluation` (script/list provenance only — no model content taken from this repo itself) |
| Sources (content, 10 repos + 1 file, each pinned to an exact commit/URL — see table) | see below |
| Download date | 2026-07-15 |

**Retrieval — 10 pinned `git` clones** (`download <repo> <commit> <dir>`
pattern from `get-expert-models.sh`, run as plain git commands):
```
download() {
  local repo="$1" commit="$2" dir="$3"
  mkdir -p "$dir"; cd "$dir"
  git init -q
  git remote add origin "$repo"
  git fetch -q origin "$commit"
  git reset -q --hard FETCH_HEAD
  cd ..
}
download https://github.com/ogiroux/talks.git                      a837092e73024383ab0e5bbace3f6b18ffbc655d  2scxlb3tbo5bmvmwplglqils7a5uarmx-talks
download https://github.com/atdyer/alloy.git                       09cbc14fc85bfea4f95351e4c921d091ecc8b94d  3zltn65gds66b6f4q3lvbtgdkb6snmuu-alloy
download https://github.com/pron/amazon-snapshot-spec.git          9c60cb18151889d7b4c0a4ffd7de0b6fc2db0fb2  7d25ioxqmue65lp6ntzz735gpbg4fmgq-amazon-snapshot-spec
download https://github.com/nmacedo/MSV.git                        6170c1473407d75ab2949ef6dcbb243b210d009c  7z32luflamhdcixvt6nwznnud4oi6dbr-MSV
download https://github.com/BGCX261/zigbee-alloy-svn-to-git.git    020bdb6a648a547e6bf1476533b602c4badaf82a  lkicptlz3eklrbu7ppmltlkebwrvzhdq-zigbee-alloy-svn-to-git
download https://github.com/hkhojasteh/CANBus.git                  f6c7b8966de590cbb61176a919dbe49c02e733b0  oujlbmnutprdhddstyudppn7t35n43os-CANBus
download https://github.com/NVlabs/litmustestgen.git                580bd7434b7ca9206f0eccbdcffe6d212eeb0994  5x4l2fj5nfbq3cz2dumwdt57g3kig3rd-litmustestgen
download https://github.com/AlloyTools/models.git                  969f5f809c33c5f70e10b2aae1c747f6a10eac86  gumxtrzzbkrtwi7jtwyu7eibi3fwhgmf-models
download https://github.com/nadeshr/weak_atomics.git                61ee841c8710cd6d2bea2041b49291a61f840b35  x7tjf3r7wnejcplj75s2o6im45kjodhs-weak_atomics
download https://github.com/naorinh/TransForm.git                  ff5c052adbc8ad0b11f9652f4886925216242516  x7t75qqe5fr6uzitot5sdu63o7drnur5-TransForm
```
plus one directly-downloaded file (note: plain `curl` got HTTP 406 from this
host without a browser-like User-Agent; a UA header was required):
```
mkdir chord-pamela-zave && cd chord-pamela-zave
curl -sL -A "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36" \
  -o correctChord.als https://www.pamelazave.com/correctChord.als
```

**Filtering pipeline applied (reproducing, not executing, the three
`portus-evaluation` scripts):**
1. Keep only files listed in `filenames-of-all-parts-of-expert-models.txt`
   (74 top-level models + their `open`-imported dependency files) — reduced
   246 downloaded `.als` files to 98.
2. Apply `fix-models.sh`'s Alloy-6 syntax fixes: global `'` → `"`, append
   `"` after each of the 15 now-reserved keywords
   (`after,always,before,enabled,eventually,historically,invariant,modifies,
   once,releases,since,steps,triggered,until,var`) wherever they occur as a
   substring (this is a blind global substitution in the original `sed`
   script too — reproduced exactly, including that bluntness), plus 3
   model-specific patches (`dbs_inst.als` open-path casing, bitwidth bump
   for `tso_transistency_*` files, comment out two unsupported assertions in
   `birthday.als`).
3. Remove the 11 top-level models Portus doesn't support (per
   `remove-unsupported.py`'s hardcoded list, each with its stated reason —
   e.g. `(*f).(*g)` composition, higher-order quantification, fields bound
   by `univ`).
4. Drop dependency files no longer referenced by any surviving top-level
   model (mirrors `compile-top-level-file-list.py`'s second pass).

Result: **63 top-level supported models** (written to
`corpus/portus-63/models-supported.txt`, one path per line) + 10 shared
dependency/import files = **73 `.als` files on disk**, verified by
independently recomputing the same 74→63 reduction from the checked-in
`filenames-of-all-parts-of-expert-models.txt` and `remove-unsupported.py`
list rather than trusting the paper's stated number blindly.

| Metric | Value |
|---|---|
| Total size | 1020 KB |
| `.als` file count | 73 (63 top-level "supported" models + 10 shared dependencies) |
| Top-level supported model count | 63 (matches the paper/task name exactly) |
| `expect 0`/`expect 1` occurrences | 146 |
| Files with ≥1 `expect` | 23 |
| Encoding | all files ASCII/UTF-8 |

**License evidence — per source repo (this corpus is a multi-source
aggregate; license posture varies file-by-file and is materially more
complicated than the other two corpora):**

| Repo | Commit | License found | Evidence |
|---|---|---|---|
| `ogiroux/talks` | `a837092e` | **none found** | No `LICENSE`/`LICENSE.txt`/`LICENSE.md`/`COPYING` at `master` or `main`; no license mention in README. Default copyright (all rights reserved) applies absent an explicit grant. |
| `atdyer/alloy` | `09cbc14f` | **none found** | Same check, same result. |
| `pron/amazon-snapshot-spec` | `9c60cb18` | **none found** | Same check, same result. |
| `nmacedo/MSV` | `6170c147` | **none found** | Same check, same result. |
| `BGCX261/zigbee-alloy-svn-to-git` | `020bdb6a` | **none found** | Same check, same result. |
| `hkhojasteh/CANBus` | `f6c7b896` | **GPL-3.0** | `LICENSE` at repo root, `master` branch, begins "GNU GENERAL PUBLIC LICENSE / Version 3, 29 June 2007 / Copyright (C) 2007 Free Software Foundation, Inc." |
| `NVlabs/litmustestgen` | `580bd743` | **BSD-3-Clause** | `LICENSE` at repo root, `master` branch: "BSD 3-Clause License / Copyright (c) 2017, NVIDIA". |
| `AlloyTools/models` | `969f5f80` | **Apache-2.0** | `LICENSE` at repo root, `master` branch: standard Apache License 2.0 text (note: this is the *separate* `AlloyTools/models` repo, distinct from `AlloyTools/org.alloytools.alloy` vendored in §1 above — same GitHub org, different repo, own license file). |
| `nadeshr/weak_atomics` | `61ee841c` | **none found** | Same check, same result. |
| `naorinh/TransForm` | `ff5c052a` | **GPL-3.0** | `LICENSE` at repo root, `master` branch, same GPLv3/FSF text as CANBus above. |
| `correctChord.als` (Pamela Zave, standalone file, not a repo) | n/a | **no license grant; explicit copyright notice** | File's own header: `"A MODEL IN ALLOY OF A CORRECT VERSION OF THE CHORD RING-MAINTENANCE PROTOCOL / Pamela Zave, August 2016. / Copyright AT&T Labs, Inc., 2016, 2018."` — a proprietary-style copyright notice with no accompanying permission/license text anywhere on the page or in the file. |

**Net read for mt-008 (facts, not a ruling):** two of the ten source repos
are GPL-3.0 (copyleft), one is Apache-2.0, one is BSD-3-Clause, six have
**no license at all** (default all-rights-reserved), and the single
standalone file carries an explicit copyright notice with no license grant.
This corpus is licensing-wise the most heterogeneous and highest-risk of the
three vendored here — flag prominently to whoever resolves mt-008.

**Oddity:** every `.als` file in this corpus has already been mechanically
patched for Alloy-6 syntax compatibility (step 2 above) — these are **not**
byte-identical to what's in the original upstream repos at the pinned
commits; they are `portus-evaluation`'s Alloy-6-compatible derivative of
those originals. If pristine (Alloy-5-syntax) originals are ever needed,
re-clone the same pinned commits and skip the `fix-models.sh`-equivalent
step.

---

## 4. `kodkod` — not vendored (not applicable as `.als` input)

**Investigated, not vendored.** `emina/kodkod` (GitHub, MIT license per `GET
/repos/emina/kodkod` → `license.spdx_id: MIT`) is the relational-model-finder
engine underneath Alloy's Kodkod backend. Its own test/example suite is
**pure Java**, constructing relational-logic problems directly via the
Kodkod Java API (`Relation`, `Formula`, `Bounds`, etc.) rather than parsing
any Alloy surface syntax.

**Evidence:** recursive tree listing of `emina/kodkod@master`
(`GET /repos/emina/kodkod/git/trees/master?recursive=1`) — 334 total
tracked files, file-extension histogram: 256 `.java`, 13 `.html`, 10 with no
extension, 4 `.h`, 3 `.cpp`, 2 `.md`, 1 each of `.gitignore`/`.css`/`.png`/
`.xml`/`.patch`/`.c`. **Zero `.als` files anywhere in the repo** — including
`examples/kodkod/examples/alloy/`, which sounded promising by name but
contains only `.java` files (presumably programmatic translations of known
Alloy examples into direct Kodkod API calls, not `.als` source).

**Rationale — not applicable as an `.als` conformance corpus, but flagged
for later use:** kodkod has nothing to contribute to Net 0 (`expect`-mining)
or any `.als`-file-based conformance net, because there is no `.als` input
to feed. It could become useful **later** as a *second, lower-level*
behavioral reference once mettle has its own relational-constraint solver
core: kodkod's Java test suite encodes known-correct relational-logic
problems and their expected bounds/solutions directly at the API level,
below the Alloy-to-relational-logic translation layer. That would be a
different kind of oracle than ADR-0002 describes (which is scoped to `.als`
→ verdict/count against the reference jar) — worth a future ADR of its own
if/when mettle's relational engine needs unit-level cross-checking
independent of the Alloy front end. No corpus directory was created for
this; there is nothing to vendor.

---

## Disk layout as vendored

```
corpus/                                    (git-ignored; not committed)
├── alloytools-models/
│   ├── LICENSE
│   ├── README.md
│   └── models/
│       ├── util/            (11 .als)
│       ├── book/             (appendixA, appendixE, chapter2, chapter4, chapter5, chapter6/  — 27 .als)
│       └── examples/         (algorithms, case_studies, puzzles, systems, temporal, toys, tutorial/  — 56 .als)
├── alloy4fun/
│   └── 2024-25/
│       ├── PROVENANCE.txt
│       └── *.json            (21 files, JSON-Lines format, 186,318 records total)
└── portus-63/
    ├── models-supported.txt  (63 top-level supported model paths, one per line)
    └── expert-models/
        ├── 2scxlb3tbo5bmvmwplglqils7a5uarmx-talks/                       (2 .als)
        ├── 3zltn65gds66b6f4q3lvbtgdkb6snmuu-alloy/                       (7 .als)
        ├── 5x4l2fj5nfbq3cz2dumwdt57g3kig3rd-litmustestgen/                (3 .als)
        ├── 7d25ioxqmue65lp6ntzz735gpbg4fmgq-amazon-snapshot-spec/         (2 .als)
        ├── 7z32luflamhdcixvt6nwznnud4oi6dbr-MSV/                         (16 .als)
        ├── chord-pamela-zave/                                            (1 .als)
        ├── gumxtrzzbkrtwi7jtwyu7eibi3fwhgmf-models/                      (33 .als)
        ├── lkicptlz3eklrbu7ppmltlkebwrvzhdq-zigbee-alloy-svn-to-git/     (5 .als)
        ├── oujlbmnutprdhddstyudppn7t35n43os-CANBus/                      (1 .als)
        └── x7t75qqe5fr6uzitot5sdu63o7drnur5-TransForm/                   (3 .als)
```

(kodkod: no directory — see §4.)

## Summary

| Corpus | `.als` files | Total size | `expect` occurrences | Files w/ `expect` | License posture |
|---|---|---|---|---|---|
| `alloytools-models` | 94 | 532 KB | 101 | 24 | Ambiguous MIT/Apache-2.0-in-transition (§2 of alloy6-reference.md) |
| `alloy4fun` | n/a (186,318 JSON-Lines records) | 374 MB | 301 | 59 records | CC-BY-4.0 (dataset), MIT (unrelated webapp code) |
| `portus-63` | 73 (63 top-level) | 1020 KB | 146 | 23 | Heterogeneous: 2× GPL-3.0, 1× Apache-2.0, 1× BSD-3-Clause, 6× no license, 1× copyright-only |
| `kodkod` | not vendored | — | — | — | MIT (engine itself; irrelevant, nothing vendored) |

## Follow-ups for mt-008

> **Resolved 2026-07-15 by [ADR-0006](../adr/0006-licensing-posture.md):**
> `corpus/` is local-only **permanently** (never committed/redistributed);
> the stdlib is a clean-room rewrite (upstream `util/*.als` copies here are
> test inputs only, off-limits as source material); mettle itself is
> MPL-2.0. The bullets below are preserved as the evidence that drove the
> decision.

- `portus-63` is the clear licensing hot spot: two GPL-3.0 sources
  (`hkhojasteh/CANBus`, `naorinh/TransForm`) and six no-license sources mean
  this corpus likely **cannot** be redistributed as part of mettle's own
  test suite even if mettle's own code ends up permissively licensed —
  local-use-only (conformance testing on this machine) is the safe
  assumption until mt-008 says otherwise.
- `alloytools-models` inherits the same top-level ambiguity already flagged
  in alloy6-reference.md §2 (MIT-style per-file headers vs. bundled
  Apache-2.0 `LICENSE.txt` that upstream itself says is "not valid yet").
- `alloy4fun` is the cleanest of the three: CC-BY-4.0 is an explicit,
  unambiguous grant (attribution required). Still not committed to git
  pending mt-008, per the blanket gate, but is the lowest-risk of the three
  if mt-008 ends up wanting to redistribute *some* corpus data (e.g. for a
  public scorecard) since CC-BY-4.0 permits redistribution with attribution.
- Re-run all retrieval commands above verbatim to reproduce `corpus/` from
  scratch; nothing here depends on state not captured in this file.
