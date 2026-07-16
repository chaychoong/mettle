//! Resolution warnings (resolution-doc §5.2, ADR-0008 decision 6). Warnings are
//! **secondary**: they never flip the accept/reject verdict (§0/§5.3). This
//! enum reproduces the §5.2 catalog by message stem; the resolver emits them
//! best-effort, ordered by source `Span` (§8), and `mettle check` (mt-019)
//! renders them like errors but never fails on them.
//!
//! The precise firing condition of each relevance/redundancy warning depends on
//! the top-down relevant type at every node and is intricate (resolution-doc
//! §9); mt-018 emits the high-confidence ones (unused binders, disjoint `&`)
//! and leaves the rarer relevance stems for mt-020 differential triage. This is
//! a deliberate scope call — warnings are not the rung gate.

use als_syntax::Span;

/// A non-fatal resolution warning.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ResolveWarning {
    /// A quantifier or `let` binder variable is never used in its body
    /// (resolution-doc §5.2, probe 40).
    UnusedVariable {
        /// The unused variable's name.
        name: String,
        /// Span of the binder.
        span: Span,
    },
    /// `&` whose two operands are always disjoint (resolution-doc §5.2, probes
    /// 01/42): the intersection is statically empty.
    IrrelevantIntersection {
        /// Span of the `&` expression.
        span: Span,
    },
    /// A static sig declared inside a variable subset parent, a static/var
    /// extends mismatch, or a redundant `var` (resolution-doc §3.1/§5.2).
    VarStaticMismatch {
        /// Human-facing stem describing which mismatch fired.
        detail: &'static str,
        /// Span of the offending sig.
        span: Span,
    },
    /// A function body whose tuple type is disjoint from its declared return
    /// type (resolution-doc §3.5/§5.2).
    ReturnDisjoint {
        /// Span of the function.
        span: Span,
    },
}

impl ResolveWarning {
    /// The primary span, for the by-`Span` emission order (§8).
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            ResolveWarning::UnusedVariable { span, .. }
            | ResolveWarning::IrrelevantIntersection { span }
            | ResolveWarning::VarStaticMismatch { span, .. }
            | ResolveWarning::ReturnDisjoint { span } => *span,
        }
    }
}
