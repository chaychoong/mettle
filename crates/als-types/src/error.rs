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

    // ---- mt-018: sig hierarchy (resolution-doc §3.1, §5.1) ----
    /// Two sigs (or a sig and a reserved builtin name) share a name in one
    /// module (`dup`, resolution-doc §3.1, probe 05). Also fires for a declared
    /// name equal to a reserved builtin (`univ`/`Int`/`none`).
    #[error("`{name}` is declared more than once in this module")]
    DuplicateSig {
        /// The clashing name.
        name: String,
        /// Span of the second declaration.
        span: Span,
    },

    /// Two params of one func/pred (or two names in one decl) share a name
    /// (`dup`, resolution-doc §3.5, §3.7).
    #[error("`{name}` is declared more than once")]
    DuplicateParam {
        /// The clashing name.
        name: String,
        /// Span of the second declaration.
        span: Span,
    },

    /// A sig inheritance cycle: `resolveSig` reaches a sig already on the
    /// current resolution stack (resolution-doc §3.1, probe 07).
    #[error("cyclic inheritance involving sig `{name}`")]
    CyclicInheritance {
        /// A sig on the cycle.
        name: String,
        /// Span of that sig's declaration.
        span: Span,
    },

    /// A `extends`/`in`/`=` parent sig name cannot be found (resolution-doc
    /// §3.1).
    #[error("the sig `{name}` cannot be found")]
    ParentSigNotFound {
        /// The unresolved parent name.
        name: String,
        /// Span of the parent reference.
        span: Span,
    },

    /// `extends` targets a subset sig — a sig can only extend a top-level sig or
    /// a subsignature (resolution-doc §3.1).
    #[error("a signature can only extend a toplevel signature or a subsignature, not `{name}`")]
    ExtendsSubsetSig {
        /// The subset-sig parent named in `extends`.
        name: String,
        /// Span of the parent reference.
        span: Span,
    },

    // ---- mt-018: fields (resolution-doc §3.4, §5.1) ----
    /// Two fields with the same label in one sig (resolution-doc §3.4).
    #[error("field `{name}` is declared more than once in this sig")]
    DuplicateField {
        /// The clashing field label.
        name: String,
        /// Span of the second field.
        span: Span,
    },

    /// A non-defined field bound contains a func/pred call (resolution-doc
    /// §3.4).
    #[error("field `{name}` declaration cannot contain a function or predicate call")]
    FieldBoundHasCall {
        /// The field label.
        name: String,
        /// Span of the offending bound.
        span: Span,
    },

    /// A field bound to the empty set / empty relation (resolution-doc §3.4).
    #[error("cannot bind field `{name}` to the empty set or empty relation")]
    FieldBoundEmpty {
        /// The field label.
        name: String,
        /// Span of the offending bound.
        span: Span,
    },

    /// Two overlapping sigs declare a same-named field (`rejectNameClash`,
    /// resolution-doc §3.4 phase 9, probe 06).
    #[error("field `{name}` is declared in two overlapping signatures")]
    FieldNameClash {
        /// The clashing field label.
        name: String,
        /// Span of the second field.
        span: Span,
    },

    // ---- mt-018: expression typing (resolution-doc §4, §5.1) ----
    /// A name in an expression resolves to nothing in scope (`hint`,
    /// resolution-doc §4.4, probes 08/09).
    #[error("the name `{name}` cannot be found")]
    UnknownName {
        /// The unresolved name.
        name: String,
        /// Span of the reference.
        span: Span,
    },

    /// An operator was applied to operands of incompatible arity
    /// (`ExprBinary.error`, resolution-doc §4.2, probe 13).
    #[error("`{op}` can be used only between expressions of compatible arity")]
    ArityMismatch {
        /// The operator symbol.
        op: &'static str,
        /// Span of the operator expression.
        span: Span,
    },

    /// A name/call is ambiguous: more than one candidate survives the
    /// disambiguation ladder (`ExprChoice.resolveHelper`, resolution-doc §4.4,
    /// probe 15).
    #[error("the name `{name}` is ambiguous due to multiple matches")]
    AmbiguousName {
        /// The ambiguous name.
        name: String,
        /// Span of the reference.
        span: Span,
        /// Human-readable candidate descriptions (the reference's reasons).
        candidates: Vec<String>,
    },

    /// An expression is used where a **formula** is required but its type is a
    /// relational value, not boolean (`typecheck_as_formula`, resolution-doc
    /// §4.3). E.g. a set expression as a fact/pred body or a quantifier body.
    #[error("this must be a formula expression")]
    NotFormula {
        /// Span of the offending expression.
        span: Span,
    },

    /// An expression is used where a **set/relation** is required but its type
    /// is boolean (`typecheck_as_set`, resolution-doc §4.3). E.g. a formula as
    /// the operand of `+`, `.`, `some`, or a field bound.
    #[error("this must be a set or relation")]
    NotSet {
        /// Span of the offending expression.
        span: Span,
    },

    /// An expression is used where an **integer** is required but its type is
    /// neither a primitive int nor an `Int` relation (`typecheck_as_int`,
    /// resolution-doc §4.3). E.g. a non-int operand of `<`, `>`, or `fun/add`.
    #[error("this must be an integer expression")]
    NotInt {
        /// Span of the offending expression.
        span: Span,
    },

    /// `~`/`^`/`*` applied to an operand that is not a binary relation
    /// (`ExprUnary` bottom-up, resolution-doc §4.2). The reference message is
    /// "`{op}` can be used only with a binary relation."
    #[error("`{op}` can be used only with a binary relation")]
    UnaryNotBinary {
        /// The operator symbol (`~`/`^`/`*`).
        op: &'static str,
        /// Span of the operator expression.
        span: Span,
    },

    /// A relational join whose touching columns are disjoint, so the join type
    /// is empty and the node is not a valid function/predicate call either
    /// (`ExprBadJoin`, resolution-doc §4.2/§4.4). The reference message is
    /// "This cannot be a legal relational join …".
    ///
    /// **Deferred — never constructed yet** (mt-020): mettle's coarse join
    /// typing cannot distinguish a genuinely illegal join from a
    /// spuriously-empty one, and enforcing this produced more false rejects
    /// than true catches (~3,436 vs ~3,261 over alloy4fun). The variant stays
    /// so the §5.1 taxonomy row is visible; the precise-types bead (mt-022)
    /// makes it fire. See LIMITATIONS.md.
    #[error("this cannot be a legal relational join")]
    IllegalJoin {
        /// Span of the join expression.
        span: Span,
    },

    /// A failed function/predicate application — no candidate is applicable and
    /// no relational join succeeds (resolution-doc §4.4).
    #[error("`{name}` cannot be resolved; possible incorrect function/predicate call")]
    BadCall {
        /// The applied name.
        name: String,
        /// Span of the call.
        span: Span,
    },

    /// A func body's arity does not match its declared return arity
    /// (`Func.setBody`, resolution-doc §3.5, probe 35).
    #[error("function `{name}` body arity does not match its declared return type")]
    FuncBodyArity {
        /// The function name.
        name: String,
        /// Span of the body.
        span: Span,
    },

    // ---- mt-018: asserts / macros (resolution-doc §3.6, §3.7, §5.1) ----
    /// Duplicate assertion name (`addAssertion`, resolution-doc §3.6).
    #[error("the assertion `{name}` is declared more than once")]
    DuplicateAssert {
        /// The clashing assert name.
        name: String,
        /// Span of the second assert.
        span: Span,
    },

    /// Duplicate macro name (`addMacro`, resolution-doc §3.7).
    #[error("the macro `{name}` is declared more than once")]
    DuplicateMacro {
        /// The clashing macro name.
        name: String,
        /// Span of the second macro.
        span: Span,
    },

    /// More than one macro of a given name is visible at a use site
    /// (resolution-doc §4.4).
    #[error("there are multiple macros with the name `{name}`")]
    MultipleMacros {
        /// The macro name.
        name: String,
        /// Span of the use.
        span: Span,
    },

    /// Macro substitution exceeded the 20-unroll budget (`Macro`,
    /// resolution-doc §3.7).
    #[error("macro substitution too deep; possibly an infinite recursion")]
    MacroTooDeep {
        /// Span of the offending macro use.
        span: Span,
    },

    // ---- mt-018: commands (resolution-doc §3.6, §5.1) ----
    /// A `run`/`check` names a pred/fun/assert that cannot be found
    /// (`resolveCommand`, resolution-doc §3.6, probes 32/33).
    #[error("the command target `{name}` cannot be found")]
    CommandTargetNotFound {
        /// The target name.
        name: String,
        /// Span of the command.
        span: Span,
    },

    /// A command target name matches more than one pred/assert ambiguously
    /// (`resolveCommand`, resolution-doc §3.6).
    #[error("the command target `{name}` is ambiguous")]
    CommandTargetAmbiguous {
        /// The target name.
        name: String,
        /// Span of the command.
        span: Span,
    },

    /// A scope names a sig that cannot be found (`resolveCommand`,
    /// resolution-doc §3.6, probe 34).
    #[error("the sig `{name}` in a scope cannot be found")]
    ScopeSigNotFound {
        /// The scope-target sig name.
        name: String,
        /// Span of the scope entry.
        span: Span,
    },

    /// A mutable, non-top-level sig was given a scope (`resolveCommand`,
    /// resolution-doc §3.6).
    #[error("mutable sig `{name}` is not top-level and cannot have scopes assigned")]
    MutableSigScoped {
        /// The scoped sig name.
        name: String,
        /// Span of the scope entry.
        span: Span,
    },

    /// An exact scope was placed on a variable sig (`resolveCommand`,
    /// resolution-doc §3.6).
    #[error("sig `{name}` is variable, so its scope cannot be exact")]
    ExactScopeOnVar {
        /// The scoped sig name.
        name: String,
        /// Span of the scope entry.
        span: Span,
    },

    /// An exact-scope parameter (`open util/ordering[exactly …]`) bound to a
    /// variable sig (resolution-doc phase 10, §5.1 last row).
    #[error("an exactly-scoped parameter cannot be bound to a variable sig")]
    ExactParamVarSig {
        /// Span of the offending open/param.
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
            | ResolveError::OpenParamNotFound { span, .. }
            | ResolveError::DuplicateSig { span, .. }
            | ResolveError::DuplicateParam { span, .. }
            | ResolveError::CyclicInheritance { span, .. }
            | ResolveError::ParentSigNotFound { span, .. }
            | ResolveError::ExtendsSubsetSig { span, .. }
            | ResolveError::DuplicateField { span, .. }
            | ResolveError::FieldBoundHasCall { span, .. }
            | ResolveError::FieldBoundEmpty { span, .. }
            | ResolveError::FieldNameClash { span, .. }
            | ResolveError::UnknownName { span, .. }
            | ResolveError::ArityMismatch { span, .. }
            | ResolveError::AmbiguousName { span, .. }
            | ResolveError::NotFormula { span }
            | ResolveError::NotSet { span }
            | ResolveError::NotInt { span }
            | ResolveError::UnaryNotBinary { span, .. }
            | ResolveError::IllegalJoin { span }
            | ResolveError::BadCall { span, .. }
            | ResolveError::FuncBodyArity { span, .. }
            | ResolveError::DuplicateAssert { span, .. }
            | ResolveError::DuplicateMacro { span, .. }
            | ResolveError::MultipleMacros { span, .. }
            | ResolveError::MacroTooDeep { span }
            | ResolveError::CommandTargetNotFound { span, .. }
            | ResolveError::CommandTargetAmbiguous { span, .. }
            | ResolveError::ScopeSigNotFound { span, .. }
            | ResolveError::MutableSigScoped { span, .. }
            | ResolveError::ExactScopeOnVar { span, .. }
            | ResolveError::ExactParamVarSig { span } => *span,
        }
    }
}
