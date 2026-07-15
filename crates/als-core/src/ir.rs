//! The relational IR: what the resolved, type-checked model lowers into and
//! what translation-to-CNF consumes.
//!
//! Unlike the surface AST (one unified `Expr`), the IR splits into three
//! sorts — [`Formula`] (boolean), [`RelExpr`] (relation-valued), and
//! [`IntExpr`] (integer-valued) — because after type checking the sort of
//! every node is known and the translator wants that split statically. The
//! *behavioral* role matches Kodkod's formula/expression/int-expression
//! split; the shape is our own (`PORTING_RULES` prime directive, R1/R2a).
//!
//! Every node keeps the [`Span`] of the surface construct it was lowered
//! from (STYLE G2), so solver-side diagnostics still point at source.

use als_syntax::{define_id, Arena, Span};

define_id! {
    /// Index into [`Ir::formulas`].
    pub struct FormulaId;
}

define_id! {
    /// Index into [`Ir::rel_exprs`].
    pub struct RelExprId;
}

define_id! {
    /// Index into [`Ir::int_exprs`].
    pub struct IntExprId;
}

define_id! {
    /// Index into [`Ir::relations`] — a free relation the solver assigns
    /// (sigs, fields, skolem constants).
    pub struct RelId;
}

define_id! {
    /// Index into [`Ir::vars`] — a variable bound by a quantifier,
    /// comprehension, or `sum`.
    pub struct VarId;
}

/// One lowered problem: arenas for all three sorts plus declarations.
///
/// Allocation order is deterministic (it follows lowering order, which
/// follows resolved source order) — `RelId` order is *the* relation order
/// used for variable numbering downstream (STYLE D2).
#[derive(Debug, Default)]
pub struct Ir {
    /// Boolean-sorted nodes.
    pub formulas: Arena<FormulaId, Formula>,
    /// Relation-sorted nodes.
    pub rel_exprs: Arena<RelExprId, RelExpr>,
    /// Integer-sorted nodes.
    pub int_exprs: Arena<IntExprId, IntExpr>,
    /// Free relations the solver assigns.
    pub relations: Arena<RelId, Relation>,
    /// Bound variables.
    pub vars: Arena<VarId, Var>,
}

/// A free relation: something the solver picks tuples for.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Relation {
    /// Diagnostic name (e.g. `this/Node`, `this/Node.next`, a skolem name).
    pub name: String,
    /// Arity (>= 1).
    pub arity: usize,
    /// Span of the declaring source construct.
    pub span: Span,
}

/// A quantifier/comprehension/`sum`-bound variable.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Var {
    /// Diagnostic name as written in source.
    pub name: String,
    /// Arity — 1 for ordinary quantification; higher arities appear when
    /// desugaring multiplicity-bound declarations.
    pub arity: usize,
    /// Span of the binding occurrence.
    pub span: Span,
}

/// A boolean-sorted node.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Formula {
    /// What kind of node this is.
    pub kind: FormulaKind,
    /// Surface construct this was lowered from.
    pub span: Span,
}

/// Formula node kinds. No catch-all `_` in matches (`PORTING_RULES` R1).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FormulaKind {
    /// Constant true/false.
    Const(bool),
    /// Negation.
    Not(FormulaId),
    /// N-ary conjunction (n-ary to keep lowering flat and sharing-friendly).
    And(Vec<FormulaId>),
    /// N-ary disjunction.
    Or(Vec<FormulaId>),
    /// Implication.
    Implies {
        /// Antecedent.
        antecedent: FormulaId,
        /// Consequent.
        consequent: FormulaId,
    },
    /// Bi-implication.
    Iff(FormulaId, FormulaId),
    /// Relational comparison.
    RelCompare {
        /// Operator.
        op: RelCmpOp,
        /// Left operand.
        lhs: RelExprId,
        /// Right operand.
        rhs: RelExprId,
    },
    /// Integer comparison.
    IntCompare {
        /// Operator.
        op: IntCmpOp,
        /// Left operand.
        lhs: IntExprId,
        /// Right operand.
        rhs: IntExprId,
    },
    /// Multiplicity test on a relation expression.
    MultTest {
        /// Which test.
        test: MultTest,
        /// Tested expression.
        expr: RelExprId,
    },
    /// Quantified formula over one variable. Surface multi-binding
    /// quantifiers and `no`/`lone`/`one` quantifiers desugar to nests of
    /// these two kinds during lowering.
    Quant {
        /// `all` or `some`.
        kind: QuantKind,
        /// The bound variable.
        var: VarId,
        /// The (unary-per-variable) bound it ranges over.
        bound: RelExprId,
        /// Body.
        body: FormulaId,
    },
    /// Unary temporal connective (Alloy 6).
    TemporalUnary {
        /// Connective.
        op: TemporalUnOp,
        /// Body.
        body: FormulaId,
    },
    /// Binary temporal connective (Alloy 6).
    TemporalBinary {
        /// Connective.
        op: TemporalBinOp,
        /// Left operand.
        lhs: FormulaId,
        /// Right operand.
        rhs: FormulaId,
    },
}

/// Primitive quantifiers after desugaring.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum QuantKind {
    /// Universal.
    All,
    /// Existential.
    Some,
}

/// Relational comparison operators.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum RelCmpOp {
    /// Subset (`in`).
    Subset,
    /// Equality.
    Equal,
}

/// Integer comparison operators.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum IntCmpOp {
    /// `=`.
    Eq,
    /// `<`.
    Lt,
    /// `=<`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
}

/// Multiplicity tests.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum MultTest {
    /// Empty.
    No,
    /// Non-empty.
    Some,
    /// At most one tuple.
    Lone,
    /// Exactly one tuple.
    One,
}

/// Unary temporal connectives (future- and past-time).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TemporalUnOp {
    /// `always`.
    Always,
    /// `eventually`.
    Eventually,
    /// `after`.
    After,
    /// `before`.
    Before,
    /// `historically`.
    Historically,
    /// `once`.
    Once,
}

/// Binary temporal connectives.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TemporalBinOp {
    /// `until`.
    Until,
    /// `releases`.
    Releases,
    /// `since`.
    Since,
    /// `triggered`.
    Triggered,
}

/// A relation-sorted node.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RelExpr {
    /// What kind of node this is.
    pub kind: RelExprKind,
    /// Surface construct this was lowered from.
    pub span: Span,
}

/// Relation-expression node kinds.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum RelExprKind {
    /// A free relation.
    Relation(RelId),
    /// A bound variable.
    Var(VarId),
    /// A relational constant.
    Const(RelConst),
    /// Binary relational operation.
    Binary {
        /// Operator.
        op: RelBinOp,
        /// Left operand.
        lhs: RelExprId,
        /// Right operand.
        rhs: RelExprId,
    },
    /// Unary relational operation.
    Unary {
        /// Operator.
        op: RelUnOp,
        /// Operand.
        expr: RelExprId,
    },
    /// The value of the operand in the next state (`e'`, Alloy 6).
    Prime(RelExprId),
    /// Conditional expression.
    IfThenElse {
        /// Condition.
        cond: FormulaId,
        /// Value when true.
        then_branch: RelExprId,
        /// Value when false.
        else_branch: RelExprId,
    },
    /// Set comprehension over unary-bound variables.
    Comprehension {
        /// Bindings, in binding order.
        decls: Vec<CompDecl>,
        /// Membership condition.
        body: FormulaId,
    },
    /// `Int[ie]` — the `Int` atom carrying an integer value.
    IntToAtom(IntExprId),
}

/// One `var: bound` binding of a comprehension.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct CompDecl {
    /// The bound variable.
    pub var: VarId,
    /// The unary bound it ranges over.
    pub bound: RelExprId,
}

/// Relational constants.
///
/// `None` and `Univ` are unary; `Iden` is binary (same as the reference
/// semantics).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum RelConst {
    /// The empty unary relation.
    None,
    /// All atoms (unary).
    Univ,
    /// The identity relation (binary).
    Iden,
}

/// Binary relational operators.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum RelBinOp {
    /// Union.
    Union,
    /// Difference.
    Diff,
    /// Intersection.
    Intersect,
    /// Relational join.
    Join,
    /// Cartesian product (`->`; multiplicity arrows desugar to formulas
    /// during lowering).
    Product,
    /// Override (`++`).
    Override,
}

/// Unary relational operators.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum RelUnOp {
    /// Transpose (binary operand).
    Transpose,
    /// Transitive closure (binary operand).
    Closure,
    /// Reflexive-transitive closure (binary operand).
    ReflexiveClosure,
}

/// An integer-sorted node.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct IntExpr {
    /// What kind of node this is.
    pub kind: IntExprKind,
    /// Surface construct this was lowered from.
    pub span: Span,
}

/// Integer-expression node kinds.
///
/// Overflow semantics are NOT encoded in these types: whether an overflowing
/// operation wraps or excludes the instance is the translator's concern,
/// governed by LEDGER-001 (default: forbid).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum IntExprKind {
    /// Integer constant.
    Const(i32),
    /// Cardinality of a relation expression.
    Card(RelExprId),
    /// `int[e]` — the integer value of a set of `Int` atoms.
    AtomToInt(RelExprId),
    /// Arithmetic negation.
    Neg(IntExprId),
    /// Binary integer operation.
    Binary {
        /// Operator.
        op: IntBinOp,
        /// Left operand.
        lhs: IntExprId,
        /// Right operand.
        rhs: IntExprId,
    },
    /// `sum var: bound | body`.
    Sum {
        /// The bound variable.
        var: VarId,
        /// The unary bound it ranges over.
        bound: RelExprId,
        /// Summed integer expression.
        body: IntExprId,
    },
    /// Conditional expression.
    IfThenElse {
        /// Condition.
        cond: FormulaId,
        /// Value when true.
        then_branch: IntExprId,
        /// Value when false.
        else_branch: IntExprId,
    },
}

/// Binary integer operators.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum IntBinOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Division (semantics pinned by a future Ledger entry alongside
    /// bitwidth/wraparound).
    Div,
    /// Remainder.
    Rem,
    /// Shift left.
    Shl,
    /// Sign-extending shift right.
    Sha,
    /// Zero-extending shift right.
    Shr,
}

#[cfg(test)]
mod tests {
    use super::*;
    use als_syntax::{ArenaId, FileId};

    fn span() -> Span {
        Span::new(FileId::from_index(0), 0, 1)
    }

    /// Builds `some n: Node | n in n.next` by hand; pins the IR construction
    /// shape across all three arenas.
    #[test]
    fn build_small_problem() {
        let mut ir = Ir::default();
        let node = ir.relations.alloc(Relation {
            name: "this/Node".to_owned(),
            arity: 1,
            span: span(),
        });
        let next = ir.relations.alloc(Relation {
            name: "this/Node.next".to_owned(),
            arity: 2,
            span: span(),
        });
        let n = ir.vars.alloc(Var {
            name: "n".to_owned(),
            arity: 1,
            span: span(),
        });

        let node_expr = ir.rel_exprs.alloc(RelExpr {
            kind: RelExprKind::Relation(node),
            span: span(),
        });
        let next_expr = ir.rel_exprs.alloc(RelExpr {
            kind: RelExprKind::Relation(next),
            span: span(),
        });
        let n_expr = ir.rel_exprs.alloc(RelExpr {
            kind: RelExprKind::Var(n),
            span: span(),
        });
        let joined = ir.rel_exprs.alloc(RelExpr {
            kind: RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: n_expr,
                rhs: next_expr,
            },
            span: span(),
        });
        let membership = ir.formulas.alloc(Formula {
            kind: FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: n_expr,
                rhs: joined,
            },
            span: span(),
        });
        let quant = ir.formulas.alloc(Formula {
            kind: FormulaKind::Quant {
                kind: QuantKind::Some,
                var: n,
                bound: node_expr,
                body: membership,
            },
            span: span(),
        });

        let FormulaKind::Quant {
            kind, bound, body, ..
        } = &ir.formulas[quant].kind
        else {
            panic!("expected quantifier node");
        };
        assert_eq!(*kind, QuantKind::Some);
        assert!(matches!(
            ir.rel_exprs[*bound].kind,
            RelExprKind::Relation(r) if r == node
        ));
        assert!(matches!(
            ir.formulas[*body].kind,
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                ..
            }
        ));
    }
}
