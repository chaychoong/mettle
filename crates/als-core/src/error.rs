//! Typed, spanned, render-free translation diagnostics (STYLE E1/E3/G3).
//!
//! [`TranslateError`] is the reject boundary of the translation phase — the
//! errors the reference's `ScopeComputer`/`BoundsComputer`/translator raise
//! *after* a model resolves and type-checks (translation-ref §1). mt-029 seeds
//! it with the **scope-phase** variants (every reject `ScopeComputer.compute`
//! can raise); later Rung-3 beads (bounds, lowering, solving) extend the same
//! enum. There is deliberately **no `_` catch-all** so a missing case is a
//! compile error, not a silent wrong verdict (PORTING R1).
//!
//! Errors are values: nothing is printed here (STYLE E3). The CLI (mt-036)
//! renders them through the mt-013 caret renderer, exactly like `ResolveError`.

use als_syntax::Span;
use thiserror::Error;

/// A translation-time failure. Mirrors the reference's `ErrorSyntax`/`ErrorAPI`
/// throws from `ScopeComputer`; every variant carries the `Span` needed for a
/// caret render. Where the reference throws the first it hits, mettle raises
/// the **first error by source position** so the reported error is
/// deterministic (STYLE D1).
#[derive(Clone, PartialEq, Eq, Debug, Error)]
pub enum TranslateError {
    /// An explicit scope was set on a subset (`in`/`=`) signature. A subset
    /// sig draws its atoms from its parents and can never be scoped
    /// (translation-ref §1.2).
    #[error("cannot specify a scope for the subset signature `{name}`")]
    ScopeOnSubset {
        /// The subset sig's name.
        name: String,
        /// Span of the offending scope entry.
        span: Span,
    },

    /// An explicit scope was set on an `enum` sig (`for 2 Color`). An enum's
    /// size is fixed by its members.
    #[error("you cannot set a scope on the enum `{name}`")]
    ScopeOnEnum {
        /// The enum sig's name.
        name: String,
        /// Span of the offending scope entry.
        span: Span,
    },

    /// A `String` scope was given without `exactly` (`for 2 String`). String
    /// atom counts must be exact (translation-ref §1.2).
    #[error("sig `String` must have an exact scope")]
    StringScopeNotExact {
        /// Span of the offending scope entry.
        span: Span,
    },

    /// A `one` sig was scoped to something other than 1.
    #[error(
        "sig `{name}` has the multiplicity of `one`, so its scope must be 1, and cannot be {scope}"
    )]
    OneSigScope {
        /// The sig's name.
        name: String,
        /// The offending scope value.
        scope: u32,
        /// Span of the offending scope entry.
        span: Span,
    },

    /// A `lone` sig was scoped above 1.
    #[error("sig `{name}` has the multiplicity of `lone`, so its scope must be 0 or 1, and cannot be {scope}")]
    LoneSigScope {
        /// The sig's name.
        name: String,
        /// The offending scope value.
        scope: u32,
        /// Span of the offending scope entry.
        span: Span,
    },

    /// A `some` sig was scoped to 0.
    #[error("sig `{name}` has the multiplicity of `some`, so its scope must be 1 or above, and cannot be 0")]
    SomeSigScope {
        /// The sig's name.
        name: String,
        /// Span of the offending scope entry.
        span: Span,
    },

    /// Per-sig scopes were given with no overall scope, and this top-level sig
    /// received neither an explicit nor a derivable scope (translation-ref
    /// §1.2 rule 2).
    #[error("you must specify a scope for sig `{name}`")]
    MustSpecifyScope {
        /// The unresolved sig's name.
        name: String,
        /// Span of the command whose scopes are incomplete.
        span: Span,
    },

    /// The requested integer bitwidth exceeds the reference's ceiling of 30.
    #[error("cannot specify a bitwidth greater than 30 (got {bitwidth})")]
    BitwidthTooLarge {
        /// The offending bitwidth.
        bitwidth: u32,
        /// Span of the offending scope entry / command.
        span: Span,
    },

    /// The command's goal contains a temporal operator (`always`/`until`/`'`/…
    /// or a `var` relation). Well-typed, but bounded LTL→FOL solving is Rung 6
    /// (ADR-0011): mettle lowers the operators faithfully into the IR but refuses
    /// a verdict rather than returning a wrong one (STYLE T2).
    #[error("temporal operators are parsed but not yet solvable (Rung 6): `{op}`")]
    TemporalUnsupported {
        /// The temporal construct encountered.
        op: &'static str,
        /// Span of the construct.
        span: Span,
    },

    /// A construct mettle cannot yet lower to a sound constraint (an exotic field
    /// multiplicity shape, a higher-order macro whose body cannot be replayed, a
    /// `run`/`check` target shape not yet handled). Deferred with a precise
    /// message rather than lowered to a wrong constraint (STYLE E5/T2).
    #[error("construct not yet lowerable (Rung 3): {what}")]
    LoweringUnsupported {
        /// A short description of the unsupported construct.
        what: String,
        /// Span of the construct.
        span: Span,
    },

    /// The command's goal requires **higher-order quantification that cannot be
    /// skolemized** (translation-ref §2.3/§10.6): a higher-order decl — one
    /// ranging over sub-relations (`some r: set A`, `some f: A one -> one B`) or a
    /// relation-valued run-pred param — at **universal** polarity, or nested in
    /// the scope of a universal quantifier. mettle skolemizes effective-existential
    /// HO decls into free relations; the rest are exactly what the reference's
    /// `HigherOrderDeclException` rejects, so mettle raises the same message as a
    /// typed defer (never a wrong verdict, STYLE E5). The bound whose upper set
    /// mettle could not soundly abstract also lands here (a decl bound depending on
    /// an outer variable, a comprehension, an `Int[·]` cast).
    #[error("Analysis cannot be performed since it requires higher-order quantification that could not be skolemized")]
    HigherOrder {
        /// Span of the offending higher-order decl.
        span: Span,
    },

    /// Encoding this command outgrew the configured effort budget
    /// ([`crate::SolveOptions::encode_budget`]) — a **resource guard**, not a
    /// model reject: the goal is well-formed but grounding it would exhaust
    /// memory or time. The analogue of the reference's engine capacity errors
    /// (the baseline's jar-side `Error` bucket); never a wrong verdict
    /// (STYLE E5).
    #[error("the problem is too large to encode: exceeded the encode budget of {cap}")]
    CapacityExceeded {
        /// The effort budget that was exceeded.
        cap: u64,
        /// Span of the goal node being encoded when the budget ran out.
        span: Span,
    },
}

impl TranslateError {
    /// The primary source span for the caret render.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            TranslateError::ScopeOnSubset { span, .. }
            | TranslateError::ScopeOnEnum { span, .. }
            | TranslateError::StringScopeNotExact { span }
            | TranslateError::OneSigScope { span, .. }
            | TranslateError::LoneSigScope { span, .. }
            | TranslateError::SomeSigScope { span, .. }
            | TranslateError::MustSpecifyScope { span, .. }
            | TranslateError::BitwidthTooLarge { span, .. }
            | TranslateError::TemporalUnsupported { span, .. }
            | TranslateError::LoweringUnsupported { span, .. }
            | TranslateError::HigherOrder { span }
            | TranslateError::CapacityExceeded { span, .. } => *span,
        }
    }
}
