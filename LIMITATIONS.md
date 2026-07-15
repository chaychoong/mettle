# Limitations

**Status:** living document · honest and current. This file shrinks as rungs are completed. It never silently lies: anything mettle cannot yet do exactly is listed here, and unsupported constructs fail loudly ("parsed, not yet solvable"), never wrongly.

## Right now (Rung 1 in progress)
mettle can lex and parse `.als` files (167/167 corpus rate) but has no user-facing entry point yet — the pretty-printer, diagnostics, and a `parse` CLI subcommand complete Rung 1. Everything past syntax (resolve, solve, visualize) is "not yet implemented"; see [docs/ROADMAP.md](docs/ROADMAP.md).

### Known syntax-level divergences from the reference (tracked, deliberate)
- **`steps`-scope validity checks deferred to resolve.** The jar rejects `for 1:2 steps` (increment must be 1) and unbounded steps not starting at 1 at command-build time; mettle currently parses these and will enforce the same checks when trace scopes are resolved (Rung 6). Never a wrong verdict — commands don't solve yet.
- **Identifier Unicode classes approximate Java's** (`char::is_alphabetic`/`is_alphanumeric` vs `isJavaIdentifierStart/Part`); divergence is only possible for exotic non-ASCII identifiers, none observed in any corpus. See [docs/reference/alloy6-grammar.md](docs/reference/alloy6-grammar.md) §1.4.
- **Unterminated block comments** are a precise error in mettle; the reference's generated lexer silently ignores a `/*` that never closes. Impossible to hit on well-formed input.

## How this file will be maintained
- As each rung lands, its capability moves out of "limitations" and the conformance scorecard records the exact agreement level.
- Constructs that parse but aren't yet solvable are listed explicitly and fail with a precise "not yet supported" diagnostic — never a wrong answer.
- Known permanent v1 non-goals (per plan §1): no native GUI (Sterling + CLI only), no unbounded model checking in v1 (temporal is bounded first), no obscure/rarely-used syntax corners until tracked here.
