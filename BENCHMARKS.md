# Benchmarks

This file holds mettle's measured speed comparisons against the reference
Alloy 6.2.0 jar. Correctness is a different question with a different
method; its scorecard lives in [README.md](README.md) and
[docs/STATE.md](docs/STATE.md).

All figures below were measured on 2026-08-27, on one machine: a MacBook Pro
(10-core Apple silicon, 64 GB RAM, macOS 26), mettle v0.1.3 in a release
build with its compiled-in CaDiCaL 1.9.5, the jar under OpenJDK 21. The
workload is the committed corpora (alloytools-models plus portus-63: 167
files, 564 `run`/`check` commands). Timings vary run to run and machine to
machine; treat every number as one honest sample, not a guarantee. The
commands to reproduce everything are at the end.

## Startup

mettle is a native binary; the jar needs a JVM. On a fresh process per file
(how interactive CLI use behaves), the jar's median is **164 ms** per file,
startup included, over a size-spread 10-file sample. mettle's median for the
same whole job is **1.1 ms**. This gap is fixed overhead, so it dominates
exactly the small, frequent invocations a CLI sees most.

## Parse and resolve

Parse plus resolve over the whole 167-file corpus, mettle against the jar's
own batch API:

| | mettle | Alloy jar |
|---|---|---|
| whole corpus, one process | **63.3 ms** | 1,336 ms (one JVM, startup amortized; 1,267 ms in-JVM) |
| median per file | **1.06 ms** | 5.27 ms (in-JVM) / 164 ms (cold JVM, startup included) |

The batch row is the like-for-like comparison, about **21 times faster** as
whole-corpus wall clock. Two caveats, which the bench tool prints itself:
mettle's total uses thread parallelism while the jar's batch API is
single-threaded, so the ratio is not a single-core claim (the single-core
comparison is the median row, about 5x); and the jar has no separate
parse-only timing, so both sides are measured as one fused parse+resolve
pass.

## Solve

A per-command head-to-head over every corpus command: the jar solving with
its out-of-the-box default (SAT4J, a pure-Java solver), mettle with its
compiled-in CaDiCaL. Both sides run one command at a time. The jar is timed
inside the JVM (startup excluded, one JVM per file, 60 s per-file timeout);
mettle runs single-threaded through the same pipeline and budgets the
conformance sweep uses (symmetry 20, `noOverflow` on, 1M conflicts / 256M
encode budget). Only commands where **both** sides produce a verdict are
compared, and the tool asserts the verdicts agree on every compared row.

Result over the corpus, 2026-08-27: **362 commands compared, and the
verdicts agreed on all 362.**

| | mettle (CaDiCaL) | Alloy jar (SAT4J) |
|---|---|---|
| total over the 362 compared commands | **43.8 s** | 123.4 s |
| median per command | **6.5 ms** | 86.5 ms |

The totals put mettle at about **2.8 times faster** end to end and the
median at about 13 times, which says the advantage is broad, not carried by
one outlier. It is not uniform: the largest single gap is `hotel4.als [0]`
(UNSAT, 32.8 s against 3.7 s), while a handful of rows go the other way
(`c11_perturbed.als [7]`, SAT, is 1.9 s on the jar against 5.3 s here). The
tool prints the top 20 rows by jar time so both kinds are visible.

The excluded rows are all typed and printed. The big bucket is the jar's
60 s per-file timeout, which removes 194 command slots — the timeout is per
file, so one slow command drags every command in its file out of the
comparison, and the heaviest files (where solver strength would matter most)
are exactly the ones it removes. The rest: 2 mettle budget defers, 6 rows
both sides decline (higher-order and unbounded-steps commands), and 24
slots in opened-module files that the conformance gauge does not count as
root commands.

Read this section with its design caveat in mind: the solver difference is
deliberate. CaDiCaL against SAT4J measures the products as shipped, not the
engines on equal footing; Alloy can be pointed at native MiniSat or Glucose,
which would narrow the gap. The excluded rows are typed and listed by the
tool: mettle's budget defers, the jar's file timeouts, and the
constructs where either side declines to answer.

## What these numbers do not claim

One machine, one run, one workload. The corpus skews toward small teaching
models, so the totals say more about overhead than about solver throughput;
the per-command table is the fairer view of solving. Determinism claims
(byte-identical output for a fixed build) are separate from speed and are
gated in CI, not here.

## Reproduce

```sh
./scripts/fetch-corpora.sh                    # corpora are fetched, never committed
cargo build --release -p als-conform -p mettle
./target/release/conform bench                # startup + parse/resolve table
./target/release/conform bench --solve        # solve head-to-head
```

Both bench modes need the reference jar at `oracle/org.alloytools.alloy.dist.jar`
(see [docs/reference/alloy6-reference.md](docs/reference/alloy6-reference.md)
for the pinned version and SHA-256). `--only <substring>` scopes `--solve`
to a file subset; `--json <path>` writes the raw per-command artifact.
