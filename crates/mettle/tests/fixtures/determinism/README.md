# The cross-target determinism suite (ADR-0019 / mt-089)

Four models `scripts/backend-determinism.sh` solves under every compiled-in SAT
backend so the resulting output hashes can be diffed across release targets.

They are chosen for one property the rest of the fixtures lack: **the search
actually has to work**. A scope-2 model is decided by propagation alone, so
every solver on every machine agrees trivially and a battery over it would prove
nothing. These four each force conflicts, and three of them have many satisfying
instances — so *which* instance is reported is a genuine heuristic choice, which
is precisely what a cross-platform floating-point difference inside CaDiCaL's
restart EMAs would perturb.

| model | shape | why |
|---|---|---|
| `pigeonhole.als` | UNSAT | a resolution-hard core: no verdict without conflict analysis |
| `queens.als` | SAT, many models | placement search; the instance shown is a heuristic artifact |
| `coloring.als` | SAT, many models | symmetry-rich graph colouring, exercises the SBP + search together |
| `handshake.als` | SAT, arithmetic | puts the integer encoding in the search loop alongside the relational structure |

They are also deliberately **fast** — the whole battery runs in ~0.1s on a
release build — because a battery that takes minutes per target will not be run.

Measured on `aarch64-apple-darwin` (2026-07-30), the suite discriminates: under
`--solver cadical`, `pigeonhole` and `queens` hash **identically** to the own
CDCL while `coloring` and `handshake` hash **differently** (a different
satisfying instance, same verdict). So two of the four rows are live signal for a
cross-target diff, and the `mettle` rows are the control that must never move.
