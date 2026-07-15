# mettle

**A conformance-tested reimplementation of Alloy 6 as a single static binary.** No JVM. Reads standard `.als` files — the same vocabulary as the reference Alloy Analyzer — finds instances and counterexamples, and (soon) visualizes them in Sterling from a first-class CLI.

> ⚠️ **Early development.** mettle is being built rung by rung; today it is in foundations. See [what it can and can't do yet](LIMITATIONS.md) and the [roadmap](docs/ROADMAP.md). It is deliberately *not* "Alloy but better" — it aims to be **Alloy, exactly**, then earn the right to diverge.

## The measure of success
mettle's goal is to be a **drop-in replacement for the latest Alloy**. That claim is not asserted — it is **measured**, by a conformance scorecard: the percentage of real Alloy models where mettle's answer matches the reference Alloy 6 jar.

**Conformance scorecard:** _(coming with the first solving rung)_

## How it's built, and how you can trust it
This project is built primarily by an AI agent fleet under human review. The credible answer to "is this just unreviewed AI output?" is **published, reproducible evidence**, not authorship claims:

- **A living conformance scorecard** measured against the reference Alloy 6 jar (pinned by exact version + SHA), regenerable by anyone.
- **Four independent testing nets:** differential verdict agreement with the jar; self-check (every instance re-verified by our own evaluator); counting (all solutions enumerated and compared at small scopes); and a model fuzzer with automatic shrinking to minimal failing `.als`.
- **A committed regression corpus:** every disagreement ever found, minimized to a tiny `.als`, kept forever.
- **Deterministic builds** and a human-owned [Semantics Ledger](SEMANTICS_LEDGER.md) of the exact behavioral rules being matched.

Note: the *product* contains no JVM. The *test infrastructure* deliberately runs the reference Alloy jar to regenerate the scorecard — that's the point.

## Install
_Coming at Rung 5._ Planned: `cargo install mettle`, `brew install mettle`, and a curl-able release binary.

## Documentation
Start at **[docs/README.md](docs/README.md)** (index) or **[docs/ROADMAP.md](docs/ROADMAP.md)** (the plan).

## License & attribution
Permissive (Apache-2.0 planned). Carries attribution/NOTICE for AlloyTools (Apache-2.0) and Kodkod (MIT); the `util/*.als` standard library is vendored verbatim with headers intact. See ADRs under [docs/adr/](docs/adr/).
