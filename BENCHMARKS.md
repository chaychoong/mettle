# Benchmarks

All figures were measured 2026-08-27 on one machine: MacBook Pro, 10-core Apple silicon, 64 GB RAM, macOS 26.

mettle v0.1.3 uses a release build with compiled-in CaDiCaL 1.9.5. The reference Alloy Analyzer 6.2.0 jar runs under OpenJDK 21.

The workload is the committed corpora, alloytools-models plus portus-63. It has 167 files and 564 run/check commands.

Timings vary between runs and machines. Each figure is one honest sample, not a guarantee. Use the reproduce commands below to repeat them.

This document reports speed. See [README.md](README.md) and [docs/STATE.md](docs/STATE.md) for correctness.

## Startup

mettle is a native binary. The jar needs a JVM.

This test uses a fresh process for each file, as interactive CLI use does. It uses a size-spread 10-file sample. The jar median is 164 ms per file, including startup. mettle's median for the same whole job is 1.1 ms.

The gap is fixed overhead. It matters most for small, frequent invocations, which a CLI mostly sees.

## Parse and resolve

This table covers the whole 167-file corpus. The jar uses its batch API.

| Measure | mettle | jar |
| --- | ---: | ---: |
| Whole corpus, one process | 63.3 ms | 1,336 ms |
| Median per file | 1.06 ms | 5.27 ms in-JVM, 164 ms cold JVM |

The jar's whole-corpus timing uses one JVM with startup amortized. It spends 1,267 ms in the JVM.

The whole-corpus row is the like-for-like comparison. mettle is about 21 times faster by whole-corpus wall clock.

mettle's total uses thread parallelism. The jar's batch API is single-threaded. The ratio is not a single-core claim. The median row is the single-core comparison, about 5x.

The jar has no separate parse-only timing. Both sides measure one fused parse+resolve pass.

## Solve

This test compares every corpus command head to head. The jar uses its out-of-the-box default, SAT4J, a pure-Java solver. mettle uses compiled-in CaDiCaL.

Both sides run one command at a time. The jar is timed inside the JVM. Startup is excluded. It uses one JVM per file and a 60 s per-file timeout. mettle runs single-threaded through the same pipeline. It uses the conformance-sweep budgets: symmetry 20, noOverflow on, 1M conflicts / 256M encode budget.

The comparison includes only commands where both sides produce a verdict. The tool asserts verdict agreement on every compared row.

On 2026-08-27, 362 commands were compared. The verdicts agreed on all 362.

| Measure | mettle | jar |
| --- | ---: | ---: |
| Total over the 362 compared commands | 43.8 s | 123.4 s |
| Median per command | 6.5 ms | 86.5 ms |

The totals put mettle at about 2.8 times faster. The median puts it at about 13 times faster. The median shows a broad advantage across commands.

Results vary by command. The largest single gap is `hotel4.als [0]`, UNSAT: 32.8 s for the jar and 3.7 s for mettle. Some rows favour the jar. `c11_perturbed.als [7]`, SAT, takes 1.9 s for the jar and 5.3 s for mettle. The tool prints the top 20 rows by jar time.

The tool prints typed exclusions. The jar's 60 s per-file timeout is the largest bucket. It removes 194 command slots. The timeout applies to a file, so one slow command removes every command in that file. The heaviest files, where solver strength matters most, are removed.

The remaining exclusions are 2 mettle budget defers, 6 rows where both sides decline higher-order and unbounded-steps commands, and 24 slots in opened-module files that the conformance gauge does not count as root commands.

The solver difference is deliberate. CaDiCaL against SAT4J measures the products as shipped, not engines on equal footing. Alloy can use native MiniSat or Glucose. Those solvers would narrow the gap.

## Scope

These results cover one machine, one run, and one workload. The corpus skews toward small teaching models. The totals therefore say more about overhead than solver throughput. The per-command view is fairer for solving.

Determinism is a separate claim. CI gates byte-identical output for a fixed build. This document does not measure it.

## Reproduce

```sh
./scripts/fetch-corpora.sh                    # corpora are fetched, never committed
cargo build --release -p als-conform -p mettle
./target/release/conform bench                # startup + parse/resolve table
./target/release/conform bench --solve        # solve head-to-head
```

Both bench modes need the reference jar at `oracle/org.alloytools.alloy.dist.jar`. See [docs/reference/alloy6-reference.md](docs/reference/alloy6-reference.md) for the pinned version and SHA-256.

`--only <substring>` scopes `--solve` to a file subset. `--json <path>` writes the raw per-command artifact.
