//! Resolution warnings (resolution-doc §5.2, ADR-0008 decision 6). Warnings are
//! **secondary**: they never flip the accept/reject verdict (§0/§5.3). This
//! enum reproduces the full §5.2 catalog; the resolver emits each variant under
//! the reference's exact firing condition (source-verified at commit
//! `794226dd`, mt-023), ordered by source `Span` (§8). `mettle check` renders
//! them like errors but never fails on them (unless `--strict`).
//!
//! ## Warning classes (the mt-023 parity vocabulary)
//! Each variant maps to a stable **class** string ([`ResolveWarning::class`]).
//! The warning-parity gauge compares per-file *sets* of `(class, position)`
//! between mettle and the reference jar (wording ignored, §8 order incidental);
//! the jar side maps message stems to the same class strings via
//! [`jar_stem_class`]. The two must agree on the vocabulary — keep them in sync.
//!
//! ## Positions
//! The reference attaches operator warnings (`&`, `.`, `<:`, …) to the operator
//! `Pos`; mettle's surface AST carries one `Span` per node (no separate
//! operator span, and adding one would touch `als-syntax`, out of scope for
//! mt-023), so a binary-operator warning lands at the node's start (the left
//! operand) rather than the operator glyph. This shifts the *column* but not the
//! *line*; the gauge therefore matches at line granularity and reports column
//! agreement as a secondary metric (see `docs/reference/warning-parity.md`).
//! Prefix-unary and sub-expression warnings (closure `^`, `int[]`, unused
//! binder, ITE branch, function-return-disjoint) do land column-exact.

use als_syntax::Span;

/// A non-fatal resolution warning (resolution-doc §5.2).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ResolveWarning {
    /// A quantifier or `let` binder variable is never used in its body
    /// (`ExprQt`/`ExprLet`, resolution-doc §5.2 B, probe 40). Position: the
    /// variable name.
    UnusedVariable {
        /// The unused variable's name.
        name: String,
        /// Span of the variable name.
        span: Span,
    },
    /// A transitive closure `^r` whose domain and range are statically disjoint
    /// (`this.type.join(this.type).hasNoTuple()`, `ExprUnary` A1). Fires only
    /// for `^` (never `~`/`*`). Position: the operator.
    ClosureRedundant {
        /// Span of the closure expression.
        span: Span,
    },
    /// A `~`/`^`/`*` whose contribution to the parent's relevant type is empty
    /// (`s == EMPTY && p.hasTuple()`, `ExprUnary` A2). Position: the operand.
    DoesNotContribute {
        /// Span of the operand sub-expression.
        span: Span,
    },
    /// An `int[e]` cast whose operand can hold no `Int` atoms
    /// (`sub.type.intersect(SIGINT).hasNoTuple()`, `ExprUnary` A5, CAST2INT).
    /// Position: the operand.
    IntAtoms {
        /// Span of the operand sub-expression.
        span: Span,
    },
    /// An `=`/`!=` whose sides are always disjoint or always identical
    /// (`ExprBinary` A3). Position: the operator.
    EqRedundant {
        /// Span of the comparison.
        span: Span,
    },
    /// An `in`/`!in` that is statically redundant — a side empty, disjoint, or
    /// identical (`ExprBinary` A4). Position: the operator.
    SubsetRedundant {
        /// Span of the comparison.
        span: Span,
    },
    /// An `&` whose two operands are always disjoint (`this.type.hasNoTuple()`,
    /// `ExprBinary` A6, probes 01/42). Position: the operator.
    IntersectIrrelevant {
        /// Span of the `&` expression.
        span: Span,
    },
    /// A `+`/`++` one of whose operands does not contribute to the relevant
    /// type (`ExprBinary` A7). Position: the operator.
    PlusIrrelevant {
        /// Span of the union/override expression.
        span: Span,
    },
    /// A `-` whose right operand is redundant (`type.hasNoTuple() ||
    /// (p&right).hasNoTuple()`, `ExprBinary` A8). Position: the operator.
    MinusIrrelevant {
        /// Span of the difference expression.
        span: Span,
    },
    /// A `.` join that statically always yields the empty set
    /// (`this.type.hasNoTuple()`, `ExprBinary` A9). Position: the operator.
    JoinEmpty {
        /// Span of the join expression.
        span: Span,
    },
    /// A `<:` domain restriction whose result is always empty (`ExprBinary`
    /// A10). Position: the operator.
    DomainIrrelevant {
        /// Span of the restriction expression.
        span: Span,
    },
    /// A `:>` range restriction whose result is always empty (`ExprBinary`
    /// A11). Position: the operator.
    RangeIrrelevant {
        /// Span of the restriction expression.
        span: Span,
    },
    /// An `->` product one of whose sides is empty while the other is not
    /// (`ExprBinary` default/A12). Position: the operator.
    ArrowIrrelevant {
        /// Span of the arrow product.
        span: Span,
    },
    /// An `if/else` (ITE) branch whose value cannot contribute to the parent's
    /// relevant type (`ExprITE` C). Position: the redundant branch.
    RedundantIteBranch {
        /// Span of the redundant branch.
        span: Span,
    },
    /// Two formulas juxtaposed on one source line with no explicit `and`
    /// (`ExprList.makeAND` implicit tag, D). Position: between the two.
    ImplicitConjunction {
        /// Span from the end of the first formula to the start of the second.
        span: Span,
    },
    /// A static sig whose parent (extends/subset) is variable (`resolveSig`
    /// E(a)/E(b)). Position: the sig.
    SigStaticVarParent {
        /// Span of the sig.
        span: Span,
    },
    /// A variable sig whose parent is static, making the `var` redundant
    /// (`resolveSig` E(c)). Position: the sig.
    SigRedundantVar {
        /// Span of the sig.
        span: Span,
    },
    /// A static field whose bound references a variable sig (`resolveFieldDecl`
    /// E(d)). Position: the field declaration.
    FieldStaticVarBound {
        /// Span of the field declaration.
        span: Span,
    },
    /// A static field inside a variable sig (`resolveFieldDecl` E(e)). Position:
    /// the field declaration.
    FieldStaticInVarSig {
        /// Span of the field declaration.
        span: Span,
    },
    /// A function whose body type is disjoint from its declared return type
    /// (`CompModule.resolveFuncBody` F). Position: the function body.
    ReturnDisjoint {
        /// Span of the function body.
        span: Span,
    },
}

impl ResolveWarning {
    /// The primary span, for the by-`Span` emission order (§8).
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            ResolveWarning::UnusedVariable { span, .. }
            | ResolveWarning::ClosureRedundant { span }
            | ResolveWarning::DoesNotContribute { span }
            | ResolveWarning::IntAtoms { span }
            | ResolveWarning::EqRedundant { span }
            | ResolveWarning::SubsetRedundant { span }
            | ResolveWarning::IntersectIrrelevant { span }
            | ResolveWarning::PlusIrrelevant { span }
            | ResolveWarning::MinusIrrelevant { span }
            | ResolveWarning::JoinEmpty { span }
            | ResolveWarning::DomainIrrelevant { span }
            | ResolveWarning::RangeIrrelevant { span }
            | ResolveWarning::ArrowIrrelevant { span }
            | ResolveWarning::RedundantIteBranch { span }
            | ResolveWarning::ImplicitConjunction { span }
            | ResolveWarning::SigStaticVarParent { span }
            | ResolveWarning::SigRedundantVar { span }
            | ResolveWarning::FieldStaticVarBound { span }
            | ResolveWarning::FieldStaticInVarSig { span }
            | ResolveWarning::ReturnDisjoint { span } => *span,
        }
    }

    /// The stable warning-class string (the mt-023 parity vocabulary). The jar
    /// side maps message stems to these same strings ([`jar_stem_class`]).
    #[must_use]
    pub fn class(&self) -> &'static str {
        match self {
            ResolveWarning::UnusedVariable { .. } => "unused-var",
            ResolveWarning::ClosureRedundant { .. } => "closure-redundant",
            ResolveWarning::DoesNotContribute { .. } => "not-contribute",
            ResolveWarning::IntAtoms { .. } => "int-atoms",
            ResolveWarning::EqRedundant { .. } => "eq-redundant",
            ResolveWarning::SubsetRedundant { .. } => "subset-redundant",
            ResolveWarning::IntersectIrrelevant { .. } => "intersect-irrelevant",
            ResolveWarning::PlusIrrelevant { .. } => "plus-irrelevant",
            ResolveWarning::MinusIrrelevant { .. } => "minus-irrelevant",
            ResolveWarning::JoinEmpty { .. } => "join-empty",
            ResolveWarning::DomainIrrelevant { .. } => "domain-irrelevant",
            ResolveWarning::RangeIrrelevant { .. } => "range-irrelevant",
            ResolveWarning::ArrowIrrelevant { .. } => "arrow-irrelevant",
            ResolveWarning::RedundantIteBranch { .. } => "redundant-ite-branch",
            ResolveWarning::ImplicitConjunction { .. } => "implicit-conjunction",
            ResolveWarning::SigStaticVarParent { .. } => "sig-static-var-parent",
            ResolveWarning::SigRedundantVar { .. } => "sig-redundant-var",
            ResolveWarning::FieldStaticVarBound { .. } => "field-static-var-bound",
            ResolveWarning::FieldStaticInVarSig { .. } => "field-static-in-var-sig",
            ResolveWarning::ReturnDisjoint { .. } => "return-disjoint",
        }
    }
}

/// Maps a reference-jar warning **message stem** (its first line) to the mt-023
/// class string, or `None` if unrecognized. This is the jar-side half of the
/// parity vocabulary — it MUST agree with [`ResolveWarning::class`]. Derived
/// from the exact §5.2 message strings (source-verified at commit `794226dd`).
#[must_use]
pub fn jar_stem_class(msg: &str) -> Option<&'static str> {
    // Compare against the first line only (the reference appends type detail on
    // later lines). Order matters where one stem is a prefix of another.
    let stem = msg.lines().next().unwrap_or(msg).trim();
    let c = if stem == "This variable is unused." {
        "unused-var"
    } else if stem.contains("is redundant since its domain and range are disjoint") {
        "closure-redundant"
    } else if stem.contains("does not contribute to the value of the parent") {
        "not-contribute"
    } else if stem.contains("This expression should contain Int atoms") {
        "int-atoms"
    } else if stem.starts_with("== is redundant") {
        "eq-redundant"
    } else if stem.starts_with("Subset operator is redundant") {
        "subset-redundant"
    } else if stem.starts_with("& is irrelevant") {
        "intersect-irrelevant"
    } else if stem.starts_with("The join operation here always yields an empty set") {
        "join-empty"
    } else if stem.starts_with("<: is irrelevant") {
        "domain-irrelevant"
    } else if stem.starts_with(":> is irrelevant") {
        "range-irrelevant"
    } else if stem.starts_with("- is irrelevant") {
        "minus-irrelevant"
    } else if stem.starts_with("+ is irrelevant") || stem.starts_with("++ is irrelevant") {
        "plus-irrelevant"
    } else if stem.contains("expression of -> is irrelevant") {
        "arrow-irrelevant"
    } else if stem == "This subexpression is redundant." {
        "redundant-ite-branch"
    } else if stem.starts_with("Implicit in-line conjunction") {
        "implicit-conjunction"
    } else if stem.starts_with("Part of ") && stem.ends_with(" is static.") {
        // "Part of X is static." — a static sig under a variable parent.
        "sig-static-var-parent"
    } else if stem.starts_with("Marking sig ") && stem.contains("as var is redundant") {
        "sig-redundant-var"
    } else if stem.starts_with("Static field types with variable bound") {
        "field-static-var-bound"
    } else if stem.starts_with("Static field inside variable sig") {
        "field-static-in-var-sig"
    } else if stem.starts_with("Function return value is disjoint") {
        "return-disjoint"
    } else {
        return None;
    };
    Some(c)
}
