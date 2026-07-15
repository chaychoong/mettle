# Limitations

**Status:** living document · honest and current. This file shrinks as rungs are completed. It never silently lies: anything mettle cannot yet do exactly is listed here, and unsupported constructs fail loudly ("parsed, not yet solvable"), never wrongly.

## Right now (Pre-Rung-1)
mettle does not yet do anything a user can run — it is in foundations. Everything Alloy does is currently "not yet implemented." The first user-runnable capability is **Rung 1** (reading/parsing `.als` files); see [docs/ROADMAP.md](docs/ROADMAP.md).

## How this file will be maintained
- As each rung lands, its capability moves out of "limitations" and the conformance scorecard records the exact agreement level.
- Constructs that parse but aren't yet solvable are listed explicitly and fail with a precise "not yet supported" diagnostic — never a wrong answer.
- Known permanent v1 non-goals (per plan §1): no native GUI (Sterling + CLI only), no unbounded model checking in v1 (temporal is bounded first), no obscure/rarely-used syntax corners until tracked here.
