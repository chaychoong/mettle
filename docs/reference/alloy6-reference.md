# Alloy 6 reference implementation — verified brief

This document pins the reference implementation used as mettle's conformance
oracle (ADR-0002) and records how to drive it headlessly. Everything under
"Verified facts" was reproduced on this machine (OpenJDK 21, Linux/amd64) on
2026-07-15; commands are given verbatim so anyone can re-run them.

## Pinned oracle

| | |
|---|---|
| Project | `AlloyTools/org.alloytools.alloy` |
| Version | **6.2.0** |
| Git tag | `v6.2.0` |
| Tag commit | `59ba2033993449d483d54acad0e11a7bbf20354f` (2024-05-21) |
| Jar built from commit | `794226dd07b536fe35c5ca44b529417183cd629b` ("back to 6.2", 2024-07-09) — embedded in the jar's own `MANIFEST.MF` as `Git-SHA`; differs from the tag commit because the release asset was rebuilt off `master` after tagging (see note below) |
| Release published | 2025-01-09T16:34:04Z (release object `created_at` is 2024-05-21, `published_at` is 2025-01-09 — GitHub shows the latter as the release date) |
| Release page | https://github.com/AlloyTools/org.alloytools.alloy/releases/tag/v6.2.0 |
| Jar asset | `org.alloytools.alloy.dist.jar` |
| Download URL | https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar |
| Jar size | 21,062,377 bytes |
| SHA-256 | `6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d` |
| Requires | JDK 17+ (manifest: `osgi.ee=JavaSE;version=17`); runs fine under the OpenJDK 21 on this VM |

`v6.2.0` is confirmed the newest **stable** (non-draft, non-prerelease) release;
the full tag history is `v6.2.0 > v6.0.0 > v5.1.0 > v5.0.0.1 > (pre-releases)`.
There is no `v6.1.0`.

Store the jar at `oracle/org.alloytools.alloy.dist.jar` (already git-ignored).

---

## Verified facts

### 1. Version/provenance

```
$ curl -s https://api.github.com/repos/AlloyTools/org.alloytools.alloy/releases/latest | jq '.tag_name,.published_at,.assets[].name'
"v6.2.0"
"2025-01-09T16:34:04Z"
"org.alloytools.alloy.dist.jar"   # among other platform installers
```

```
$ curl -sL -o oracle/org.alloytools.alloy.dist.jar \
    https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar
$ sha256sum oracle/org.alloytools.alloy.dist.jar
6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d  oracle/org.alloytools.alloy.dist.jar
```

`java -jar oracle/org.alloytools.alloy.dist.jar version` prints `6.2.0`.

### 2. Licenses

**Top-level status is genuinely ambiguous — read this carefully before mettle
redistributes anything derived from Alloy source.**

- The jar bundles `META-INF/LICENSE.txt` containing the full **Apache License
  2.0** text, and `META-INF/NOTICE.txt` (Apache Commons IO attribution only —
  it does **not** mention Kodkod, SAT4J, or the `util/*.als` models).
- The repo's own root `LICENSE` file, fetched from `master`, literally begins:
  ```
  # THIS IS NOT VALID YET! CURRENTLY CODE IS UNDER MIT LICENSE

  Apache License
                             Version 2.0, January 2004
  ...
  ```
  i.e. upstream is mid-transition from MIT to Apache-2.0 and says so itself.
  GitHub's license detector accordingly reports `"license": {"key": "other",
  "spdx_id": "NOASSERTION"}` for the repo.
- Per-file headers on the actual core source (the code that matters for a
  reimplementation) are MIT-style, e.g.
  `org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/alloy4/A4Reporter.java`:
  ```
  /* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
   *
   * Permission is hereby granted, free of charge, to any person obtaining a copy of this software ...
   */
  ```
  Newer files added under the AlloyTools org (e.g.
  `org.alloytools.alloy.core/.../org/alloytools/alloy/core/infra/Alloy.java`)
  carry **no header at all**.
- The dist jar's own OSGi manifest declares `Bundle-License: MIT` /
  `Bundle-Copyright: MIT` for `org.alloytools.alloy.dist` — consistent with
  the per-file MIT headers, and in tension with the bundled Apache-2.0
  `LICENSE.txt`.
- **Practical read:** treat Alloy 6's own code as MIT-style-licensed (matches
  both the per-file headers and the manifest's `Bundle-License`), and treat
  the bundled Apache-2.0 `LICENSE.txt` as an in-progress relicensing artifact
  that upstream itself says is "not valid yet." This is not a mettle-side
  judgment call resolved here — flag it to whoever handles mettle's own
  licensing/attribution before shipping a corpus or derived text. (Task
  assumption of "expected Apache-2.0" for the analyzer itself is **not**
  confirmed as the operative license; see Unverified section.)

Bundled third-party components, confirmed by extracting `LICENSES/*.txt` from
the jar and cross-checking source headers on GitHub:

| Component | License | Evidence |
|---|---|---|
| Kodkod | MIT | `LICENSES/Kodkod.txt` in jar: `Copyright (c) 2005 - present Emina Torlak`, standard MIT text. Matches `kodkod/ast/Node.java` header on GitHub. |
| SAT4J | **LGPL 2.1** (dual EPL/LGPL upstream; the bundled `LICENSES/SAT4J.txt` here is the LGPL 2.1 text) | `LICENSES/SAT4J.txt` in jar; also the `solvers` CLI output literally says "SAT4J ... is an open-source project under the GNU LGPL license." Note: task brief did not claim SAT4J was MIT, this is just recorded for completeness — do not conflate with Kodkod's MIT license. |
| Glucose, MiniSat, Lingeling, Electrod, Gini | separate license files bundled (`LICENSES/Glucose.txt` etc.) — not needed for the zero-native-deps path (§4), not deeply audited here. |
| Apache Commons IO | Apache-2.0, per `META-INF/NOTICE.txt`. |

`util/*.als` standard library (`models/util/{boolean,graph,integer,natural,
ordering,relation,seqrel,sequence,sequniv,ternary,time}.als`, 94 `.als` files
total bundled under `models/`): no separate per-file license/copyright header
was found in the jar or in the GitHub source
(`org.alloytools.alloy.core/src/main/resources/models/util/*.als`), and there
is no dedicated NOTICE entry for them. They ship under the same
ambiguous top-level terms as the rest of the core codebase (see above).

### 3. Running headless

Main entry point (from `MANIFEST.MF`): `Main-Class:
org.alloytools.alloy.core.infra.Alloy`, which dispatches to sub-commands.
Relevant `Provide-Capability` entries: `edu.mit.csail.sdg.alloy4.
WorkerEngineFacade`, `edu.mit.csail.sdg.alloy4whole.CLIFacade`,
`org.alloytools.alloy.cli.CLI`.

Discover sub-commands:
```
$ java -jar oracle/org.alloytools.alloy.dist.jar help
```
Relevant sub-commands: `version`, `solvers`, `natives`, `prefs`, `commands`,
`exec`. (`gui` requires a display and throws `HeadlessException` with no
`DISPLAY` — confirmed; don't invoke it.)

#### 3(a) Verdict for a named command

List commands (name + index) in a model:
```
$ java -jar oracle/org.alloytools.alloy.dist.jar commands oracle/test1.als
0 . Run show for 3
1 . Check NoEmpty for 3
```

Run one by name or index, get a human-readable trace and a machine-readable
`receipt.json`:
```
$ java -jar oracle/org.alloytools.alloy.dist.jar exec -c show oracle/test1.als
00. run   show                     0    1/1     SAT
$ cat test1/receipt.json     # created next to the source file
```
`receipt.json`'s `commands.<name>.solution` is a list (one per found
instance); an empty/absent list plus the `UNSAT` summary line means no
instance was found. Exit code is `0` on success, `1` if an `expect`
annotation was violated (see §5) or on error — verified below.

Minimal test files used (kept in `oracle/` for reference):
`oracle/test1.als`, `oracle/test2.als`, `oracle/test3.als`,
`oracle/overflow.als`, `oracle/bitwidth.als`.

#### 3(b) Enumerate / count all instances at a scope

`exec -r <N>` controls how many solutions to enumerate; `-r 0` means "as many
as can be found" (exhaustive enumeration at that scope):

```
$ java -jar oracle/org.alloytools.alloy.dist.jar exec -c show -r 0 oracle/test1.als
00. run   show   0  1 2 3 4 ... 87/0   SAT
```
`receipt.json`'s `commands.show.solution` array then has **87** entries for
`test1.als`'s `show` command at `for 3` (default symmetry breaking, effort
20) — i.e. 87 is the SB-quotiented instance count. Each array element is one
instance (proved by inspecting `len(d['commands']['show']['solution'])` in
the JSON). This is the mechanism for "enumerate/count all instances for a
command at a given scope."

#### 3(c) Solver options: symmetry breaking, bitwidth, overflow

**Bitwidth** is not a global CLI flag — it's part of the Alloy scope syntax
in the command itself (`for 3 but 4 int`), same as in the language. Verified:
a command with plain `for 3` (no `but N int`) produces `"bitwidth":4` in
`receipt.json` — **4 is the default bitwidth** regardless of the overall
scope number (checked also with `for 10`, still bitwidth 4).

**Symmetry breaking — can it be set to 0, and does the CLI flag actually
work?** This matters directly for ADR-0002, which mandates running the
oracle with `symmetryBreaking = 0` for the canonical counting net.

- `exec --help` advertises `-y, --ymmetry <int>` ("default is 20") — but
  **this CLI flag is a confirmed no-op / dead due to an upstream bug.**
  Passing `--ymmetry 0` to `exec` does not change the emitted
  `"generating lex-leader symmetry breaking predicate"` Kodkod log line, does
  not change `receipt.json`'s echoed `"symmetry":20`, and does not change the
  enumerated instance count (still 87 for `test1.als`, same as the default).
  Root cause, found in the actual CLI source
  (`org.alloytools.alloy.cli/src/main/java/org/alloytools/alloy/cli/CLI.java`,
  method `_exec`):
  ```java
  opt.skolemDepth = options.depth(opt.skolemDepth);
  opt.symmetry    = options.depth(opt.symmetry);   // <-- reads --depth, not --ymmetry!
  ```
  `options.ymmetry(...)` is declared in the `ExecOptions` interface but is
  **never called anywhere**. So `-y`/`--ymmetry` is dead, and `-d`/`--depth`
  accidentally controls *both* `skolemDepth` and `symmetry` simultaneously.
  Confirmed empirically: `exec -c show -r 0 --depth 0 oracle/test1.als`
  actually does suppress the "generating lex-leader symmetry breaking
  predicate" log line and bumps the enumerated count from 87 to **1129**
  (matching the API-level result below exactly) — i.e. `--depth 0` is a
  working *accidental* alias for `--ymmetry 0` in v6.2.0, but it is fragile
  (a bug, could be "fixed" upstream any time, and also clobbers
  `skolemDepth`) and **should not be relied on**.

- **The reliable way to set `symmetryBreaking = 0` is the Java API**, not the
  CLI. `edu.mit.csail.sdg.translator.A4Options` has a plain public `int
  symmetry` field; `new A4Options()` defaults it to **20** (same default the
  CLI documents). Setting `opt.symmetry = 0` before calling
  `TranslateAlloyToKodkod.execute_command(...)` is proven to work:

  Harness (`oracle/Harness.java`, compiled with
  `javac -cp org.alloytools.alloy.dist.jar Harness.java` against the
  downloaded jar, run with
  `java -cp .:org.alloytools.alloy.dist.jar Harness <file> <cmdIndex> <symmetry> <noOverflow> <solverName>`):

  ```
  symmetry=20 (CLI-equivalent default): total distinct instances enumerated=87   (elapsed 224ms)
  symmetry=0  (no symmetry breaking):   total distinct instances enumerated=1129 (elapsed 854ms)
  ```
  The Kodkod log also confirms: with `symmetry=20` you see `detected 18
  equivalence classes of atoms ...` followed by `generating lex-leader
  symmetry breaking predicate ...`; with `symmetry=0` the second line is
  absent. This is airtight proof that `symmetryBreaking` (aka `A4Options.
  symmetry`) can be set to 0 and that it changes both the solving log and the
  enumerated-instance count exactly as expected.

  **Recommendation for mettle's `als-conform` harness (mt-006): drive the
  jar via a small compiled Java shim using `A4Options`/
  `TranslateAlloyToKodkod.execute_command`/`A4Solution.next()` (as in
  `oracle/Harness.java`), not by shelling out to `exec -y 0`.** The CLI flag
  cannot be trusted for the SB=0 canonical count that ADR-0002 depends on.

- **Overflow ("forbid overflows" / `noOverflow`) — default value.**
  `A4Options` field is `public boolean noOverflow;` and `new A4Options()`
  defaults it to **`false`** — i.e. **overflow is allowed (silently wraps,
  2's-complement) by default**, matching the CLI: `exec`'s `-n`/
  `--nooverflow` flag ("If set, the solution will include only those models
  in which no arithmetic overflows occurred") likewise defaults to unset
  (allow overflow).

  Empirical proof, `oracle/overflow.als` (`one sig S { x,y,z: Int }`,
  `x=7, y=7, z=plus[x,y]`, `for 3 but 4 int`, so range is `-8..7` and `7+7=14`
  overflows):
  ```
  $ java -jar oracle/org.alloytools.alloy.dist.jar exec -c addOverflow -t text -o - oracle/overflow.als
  this/S<:z={S$0->-2}        # SAT: 7+7 wraps to -2 (14 mod 16, signed) — overflow allowed
  $ java -jar oracle/org.alloytools.alloy.dist.jar exec -c addOverflow -n -t text -o - oracle/overflow.als
  (no instance printed — UNSAT: forbidding overflow makes 7+7=plus[...] unsatisfiable)
  ```
  Same result confirmed via the API harness (`noOverflow=false` → SAT;
  `noOverflow=true` → UNSAT).

  **Important nuance / potential trap:** the *GUI preference default*, as
  reported by `java -jar oracle/org.alloytools.alloy.dist.jar prefs`, shows:
  ```
  NoOverflow    Prevent overflows    true
  ```
  This is the compiled-in default for the **interactive GUI's stored
  preference** (confirmed to not be a leftover from a prior run — `~/.java/
  .userPrefs/edu/mit/csail/sdg/alloy4/prefs.xml` is an empty preferences map
  on this fresh VM, so `true` is what ships, not something cached). It
  disagrees with the **API/headless default** (`A4Options.noOverflow =
  false`, and `exec` without `-n` also allows overflow, as proven above).
  **Conclusion: Alloy 6.2.0's default differs depending on entry point** — the
  GUI's checkbox is checked (prevent overflow) by default, but the
  programmatic `A4Options` default and the CLI `exec` subcommand's default
  is to *allow* overflow. mettle's oracle, since it should go through the API
  or `exec` (not the interactive GUI), should treat **`noOverflow = false`
  (overflow allowed) as Alloy 6.2.0's effective headless default**, and must
  set it explicitly either way rather than assume.

### 4. Pure-Java SAT solving (zero native dependencies)

`java -jar oracle/org.alloytools.alloy.dist.jar solvers` lists solver
backends with a `type` column; **`sat4j`, `sat4j.light`, `sat4j.pmax` are all
`type=java`** (as opposed to `type=jni` for glucose/minisat or `type=external`
for lingeling.parallel/yices). `A4Options.solver` (and the `exec -s` flag)
**default to `sat4j`** — confirmed both from `new A4Options().solver` printing
`sat4j` and from the CLI help text ("The default solver is SAT4J.").

Proof of headless, zero-native-dependency operation:
```
$ java -jar oracle/org.alloytools.alloy.dist.jar exec -c show -s sat4j -t text -o - oracle/test1.als
... (SAT instance printed, exit 0)
```
No `.so`/native library was extracted or loaded for this run (checked
`find /tmp -iname '*.so' -newer <jar>` → nothing new; the only native-related
log lines seen elsewhere are `NativeCode` probing for optional external
tools — NuSMV/nuXmv/yices — which are unrelated to `sat4j` and are absent
without failing the run). SAT4J itself is `org.sat4j.*`, a pure-Java library
bundled directly in the dist jar's `Private-Package` list (confirmed in
`MANIFEST.MF`).

**This means mettle's oracle can run the reference jar on any machine with
just a JDK — no native SAT solver install required — by always passing
`-s sat4j` (CLI) or setting `A4Options.solver = SATFactory.find("sat4j").get()`
(API).**

### 5. `expect 0` / `expect 1` semantics

Empirically confirmed with `oracle/test2.als` / `oracle/test3.als`:

- `expect 0` asserts the command is **UNSAT** (no instance exists). If the
  command is actually SAT, `exec` prints `Error ... 'Run ... expect 0' was
  satisfied against expectation` and **exits with code 1**.
- `expect 1` asserts the command is **SAT** (an instance exists). If the
  command is actually UNSAT, `exec` prints `Error ... 'Run ... expect 1' was
  not satisfied against expectation` and **exits with code 1**.
- When the expectation matches the actual verdict, `exec` exits **0** and
  prints no error (verified: matching `impossible ... expect 0` against an
  actually-UNSAT predicate exits 0 cleanly).
- Source-level confirmation, `CLI.java`:
  ```java
  if (c.expects == 1) { ... error("'%s' was not satisfied against expectation", c); }
  ...
  if (c.expects == 0) { ... error("'%s' was satisfied against expectation", c); }
  ```
  and `receipt.json` records `"expects":<-1|0|1>` per command (`-1` = no
  `expect` annotation present, matching `test1.als`'s unmarked commands).

This directly supports ADR-0002's "Net 0" (mining `expect` annotations from
the corpus as a free cross-check) — the verdict and exit code are exactly
what a harness should parse.

---

## Unverified / needs follow-up

- **Which license actually governs Alloy 6.2.0 is not settled upstream**, as
  documented in §2 above (repo's own `LICENSE` file says "NOT VALID YET");
  this brief only reports what was directly observed, it does not adjudicate
  the ambiguity. Follow-up: ask/watch upstream (AlloyTools) for a
  relicensing resolution, or default to the more restrictive MIT-style
  per-file terms until clarified.
- The tag commit (`59ba2033...`) vs. the jar's embedded build commit
  (`794226dd...`, "back to 6.2") differ; not investigated further why the
  release asset was rebuilt off a later `master` commit than the tag. Does
  not affect functional pinning (the jar's SHA-256 is the actual pin), but
  if mettle ever needs to build from source to cross-check, use
  `794226dd07b536fe35c5ca44b529417183cd629b`, not the tag ref, to match the
  exact bits in the dist jar.
- Did not audit the native solvers (glucose/minisat/lingeling/yices/electrod)
  beyond confirming their bundled license files exist; irrelevant to the
  zero-native-dependency SAT4J path mettle should use, but relevant if
  mettle ever wants to cross-check against a native solver for
  bitwidth/edge-case parity.
- Did not verify whether `-y`/`--ymmetry` is fixed in any `master`
  commit newer than the pinned tag (i.e. whether this is already fixed
  post-6.2.0 and would need re-verification against a future release). Given
  ADR-0002 pins exactly 6.2.0, this doesn't block mettle today, but if the
  pinned version is ever bumped, re-run the `--ymmetry` no-op check
  (`oracle/test1.als`, compare enumerated count with/without the flag) before
  trusting it.
- `receipt.json`'s `"symmetry"` field appears to just echo a fixed/default
  value rather than the actually-used value in some cases (e.g. it was
  entirely absent from the receipt when `--depth 0` was used even though
  behavior clearly changed) — did not fully chase down why; treat
  `receipt.json`'s `symmetry` key as unreliable telemetry, not ground truth.
- Did not exhaustively test `-u/--unrolls` (recursion unrolling) or
  `-d/--depth` (skolem depth) for their *intended* purposes beyond noting the
  aliasing bug above.

## Reproduction artifacts

All kept under `oracle/` (git-ignored except this brief references them by
relative path):
- `org.alloytools.alloy.dist.jar` — the pinned oracle jar (re-download with
  the URL/SHA above; do not commit).
- `test1.als`, `test2.als`, `test3.als`, `overflow.als`, `bitwidth.als` —
  minimal hand-written models used for the empirical checks above.
- `Harness.java` / `DefaultCheck.java` — small API-level programs proving
  `A4Options` defaults and the `symmetry=0` / `noOverflow` behavior described
  above. Compile with `javac -cp org.alloytools.alloy.dist.jar Harness.java`;
  run with `java -cp .:org.alloytools.alloy.dist.jar Harness <file>
  <cmdIndex> <symmetry> <noOverflow:true|false> <solverName e.g. sat4j>`.
- `extracted/` — `LICENSE.txt`, `NOTICE.txt`, `Kodkod.txt`, `SAT4J.txt`
  pulled out of the jar for the license section above.
- `CLI.java.src` — a fetched copy of upstream's
  `org.alloytools.alloy.cli.CLI` source (for the `--ymmetry`/`--depth` bug
  citation above); not part of the jar, kept only for reference.
