//! Typed, spanned, render-free resolution diagnostics (ADR-0008 decision 6,
//! STYLE E1/E3/G3).
//!
//! [`ResolveError`] is the reject boundary of the Rung-2 resolver. This bead
//! (mt-017) seeds it with the **module-phase** variants — every reject the
//! module graph / `open` layer can raise (resolution-doc §5.1, the
//! `resolveParams`/`addOpen`/`parseRecursively` rows), plus the load-time
//! parse pass-through. mt-018 extends the same enum with the sig/field/
//! func/type variants; there is deliberately **no `_` catch-all** so a missing
//! case is a compile error, not a silent wrong verdict (PORTING R1, ADR-0008
//! decision 8).
//!
//! Errors are values: nothing is printed here (STYLE E3). `mettle check`
//! (mt-019) renders them through the mt-013 caret renderer, exactly like
//! `ParseError`.

use als_syntax::{ParseError, Span};
use thiserror::Error;

/// A resolution failure. The Rung-2 gauge (mt-020) is binary ACCEPT
/// (`Ok`) vs REJECT (`Err`); every variant carries the `Span`(s) needed for a
/// caret render. Where the reference collects into a `JoinableList` and throws
/// the first, mettle surfaces the **first error by source position** (ADR-0008
/// decision 7) so the single reported error is deterministic.
#[derive(Clone, PartialEq, Eq, Debug, Error)]
pub enum ResolveError {
    /// A transitively-`open`ed file failed to parse. The reference raises the
    /// parse error during `parseRecursively`, before `resolveAll`; mettle
    /// surfaces it as a load-phase reject carrying the offending file's path.
    #[error("could not parse opened module `{path}`: {source}")]
    OpenedFileParse {
        /// Normalized path of the file that failed to parse.
        path: String,
        /// Span of the `open` directive that pulled the file in.
        span: Span,
        /// The underlying parse failure.
        #[source]
        source: ParseError,
    },

    /// No file could be found for an `open` target after the whole search
    /// order was exhausted (computed path, verbatim, disk, `.md`, embedded
    /// stdlib — resolution-doc §2.1). While the clean-room stdlib table
    /// (mt-015) is still empty, `util/*` targets land here.
    #[error("module file for `{target}` cannot be found")]
    ModuleFileNotFound {
        /// The `open` target module path as written.
        target: String,
        /// Span of the `open` directive.
        span: Span,
    },

    /// A file appears twice on the current `open` chain (resolution-doc §2.2):
    /// a circular module import, rejected at load time.
    #[error("circular dependency in module import: `{path}`")]
    CircularImport {
        /// Normalized path of the file that closed the cycle.
        path: String,
        /// Span of the `open` directive that closed the cycle.
        span: Span,
    },

    /// Two `open`s in one module resolve to the **same alias** but different
    /// `(file, args)` (resolution-doc §2.4, probe 26). Identical re-opens are
    /// silently allowed and never reach here.
    #[error("cannot import two different modules using the same alias `{alias}`")]
    DuplicateAlias {
        /// The clashing alias.
        alias: String,
        /// Span of the second (rejected) `open`.
        span: Span,
        /// Span of the first `open` that claimed the alias.
        first_span: Span,
    },

    /// An `open`'s argument count does not match the opened module's parameter
    /// count (resolution-doc §2.3, probe 31).
    #[error("module instantiation expects {expected} argument(s), found {found}")]
    OpenArgCount {
        /// Number of parameters the opened module declares.
        expected: usize,
        /// Number of arguments supplied at the `open` site.
        found: usize,
        /// Span of the `open` directive.
        span: Span,
    },

    /// `none` supplied as an `open` argument (resolution-doc §2.3, probe 64).
    #[error("`none` cannot be used as a module instantiation argument")]
    NoneAsOpenArg {
        /// Span of the offending argument.
        span: Span,
    },

    /// After parameter substitution, an `open` argument still names a parameter
    /// of the opening module that has no binding (resolution-doc §2.3, the
    /// "unresolved param after fixpoint" reject). Sig-existence of a *concrete*
    /// argument name is checked later, by mt-018's name resolution.
    #[error("module instantiation argument `{name}` cannot be resolved")]
    OpenParamNotFound {
        /// The unresolved argument name.
        name: String,
        /// Span of the offending argument.
        span: Span,
    },
}

impl ResolveError {
    /// The primary source span of this error, for first-by-position ordering
    /// (ADR-0008 decision 7) and caret rendering.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            ResolveError::OpenedFileParse { span, .. }
            | ResolveError::ModuleFileNotFound { span, .. }
            | ResolveError::CircularImport { span, .. }
            | ResolveError::DuplicateAlias { span, .. }
            | ResolveError::OpenArgCount { span, .. }
            | ResolveError::NoneAsOpenArg { span }
            | ResolveError::OpenParamNotFound { span, .. } => *span,
        }
    }
}
