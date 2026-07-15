//! Arena-based AST for one parsed Alloy 6 module (one `.als` source file).
//!
//! Shape decisions (rationale in ADR-0005):
//! - **One unified [`Expr`].** Surface Alloy does not syntactically separate
//!   formulas from relational or integer expressions — that split happens in
//!   the type checker. The relational IR in `als-core` is where the
//!   formula/expression/int-expression split lives.
//! - **Spans are required fields** on every node (STYLE G1); constructing a
//!   node without one is a compile error.
//! - **Temporal syntax is first-class** from day one (STYLE T1): `var` sigs,
//!   primes, and the full unary/binary temporal connective set.
//! - **Cross-references are typed arena IDs** (STYLE §6, `PORTING_RULES` R3);
//!   the arenas live in [`Ast`].
//! - Names are owned `String`s for now; interning is a later, mechanical
//!   change if profiles ask for it.

use crate::{define_id, Arena, Span};

define_id! {
    /// Index into [`Ast::exprs`].
    pub struct ExprId;
}

define_id! {
    /// Index into [`Ast::decls`].
    pub struct DeclId;
}

define_id! {
    /// Index into [`Ast::paras`].
    pub struct ParaId;
}

/// One parsed module: header, opens, paragraphs, and the arenas they index.
///
/// Each phase owns its arenas (STYLE A2): the parser produces an `Ast`;
/// resolution/typing consume it and build their own structures.
#[derive(Debug, Default)]
pub struct Ast {
    /// `module` header, absent for headerless files.
    pub header: Option<ModuleHeader>,
    /// `open` directives in source order.
    pub opens: Vec<Open>,
    /// Paragraphs in source order.
    pub paragraphs: Vec<ParaId>,
    /// Paragraph arena.
    pub paras: Arena<ParaId, Para>,
    /// Expression arena.
    pub exprs: Arena<ExprId, Expr>,
    /// Declaration arena (fields, quantifier/function parameters).
    pub decls: Arena<DeclId, Decl>,
}

/// An identifier with its source location.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ident {
    /// The identifier text as written.
    pub text: String,
    /// Where it was written.
    pub span: Span,
}

/// A possibly-qualified name: `this/foo`, `ord/first`, `util/ordering`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct QualName {
    /// Path segments, at least one.
    pub segments: Vec<Ident>,
    /// Span of the whole path.
    pub span: Span,
}

/// `module path[X, exactly Y]`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ModuleHeader {
    /// Declared module path.
    pub name: QualName,
    /// Type parameters, possibly `exactly`-marked.
    pub params: Vec<ModuleParam>,
    /// Span of the whole header.
    pub span: Span,
}

/// One module type parameter.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ModuleParam {
    /// Parameter name (the grammar allows qualified names here).
    pub name: QualName,
    /// `exactly` marker.
    pub is_exact: bool,
}

/// `[private] open path[args] [as alias]`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Open {
    /// Opened module path.
    pub module: QualName,
    /// Instantiation arguments (sig references).
    pub args: Vec<QualName>,
    /// `as` alias.
    pub alias: Option<Ident>,
    /// `private` marker.
    pub is_private: bool,
    /// Span of the whole directive.
    pub span: Span,
}

/// A top-level paragraph.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Para {
    /// `sig` declaration.
    Sig(SigDecl),
    /// `enum` declaration (sugar for an abstract sig + one-sig extensions).
    Enum(EnumDecl),
    /// `fact` paragraph.
    Fact(FactDecl),
    /// `pred` paragraph.
    Pred(PredDecl),
    /// `fun` paragraph.
    Fun(FunDecl),
    /// `assert` paragraph.
    Assert(AssertDecl),
    /// Top-level `let` macro.
    Macro(MacroDecl),
    /// `run`/`check` command.
    Cmd(CmdDecl),
}

/// Name of a `fact`/`assert` paragraph: an identifier or a string literal
/// (string names are accepted by the reference grammar).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ParaName {
    /// `fact cycle_free { .. }`.
    Ident(Ident),
    /// `fact "no cycles" { .. }` — stored unescaped.
    Str {
        /// The literal's unescaped value.
        value: String,
        /// Where it was written.
        span: Span,
    },
}

/// `[qualifiers] sig A, B extends P { fields } { appended-fact }`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigDecl {
    /// Qualifiers preceding `sig`.
    pub qual: SigQual,
    /// Declared names (one `sig` can declare several).
    pub names: Vec<Ident>,
    /// `extends`/`in` clause.
    pub parent: SigParent,
    /// Field declarations.
    pub fields: Vec<DeclId>,
    /// Appended fact block, if any.
    pub fact: Option<ExprId>,
    /// Span of the whole paragraph.
    pub span: Span,
}

/// Qualifiers on a `sig` declaration.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct SigQual {
    /// `abstract`.
    pub is_abstract: bool,
    /// `var` (Alloy 6 mutable sig).
    pub is_var: bool,
    /// `private`.
    pub is_private: bool,
    /// `lone`/`one`/`some` sig multiplicity.
    pub mult: Option<SigMult>,
}

/// Multiplicity qualifier on a `sig`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SigMult {
    /// At most one atom.
    Lone,
    /// Exactly one atom.
    One,
    /// At least one atom.
    Some,
}

/// The hierarchy clause of a `sig`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SigParent {
    /// Top-level sig, no clause.
    None,
    /// `extends P` — disjoint subsignature.
    Extends(QualName),
    /// `in P + Q + ...` — (non-disjoint) subset sig of a union of sig refs.
    In(Vec<QualName>),
    /// `= P + Q + ...` — subset sig equal to a union of sig refs.
    Eq(Vec<QualName>),
}

/// `enum Name { A, B, C }`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct EnumDecl {
    /// Enum name.
    pub name: Ident,
    /// Variant names in source order (this order is semantic: it induces
    /// the enum's total order).
    pub variants: Vec<Ident>,
    /// Span of the whole paragraph.
    pub span: Span,
}

/// A declaration: sig field, quantifier binding, or pred/fun parameter.
///
/// `[var] [private] [disj] a, b : [disj] bound` — the bound expression
/// carries any multiplicity/`seq` marker as a unary [`ExprKind::Unary`]
/// node; a defined decl (`a = e`) carries [`UnOp::ExactlyOf`].
#[derive(Clone, PartialEq, Eq, Debug)]
// The grammar defines four independent, freely combinable markers; encoding
// them as anything but four bools would misstate the syntax.
#[allow(clippy::struct_excessive_bools)]
pub struct Decl {
    /// `disj` marker — declared names are pairwise disjoint.
    pub is_disj: bool,
    /// `disj` marker after the `:` — a separate flag in the grammar.
    pub is_bound_disj: bool,
    /// `var` marker (Alloy 6 mutable field).
    pub is_var: bool,
    /// `private` marker (fields only).
    pub is_private: bool,
    /// Declared names, at least one.
    pub names: Vec<Ident>,
    /// Bounding expression, including any multiplicity marker.
    pub bound: ExprId,
    /// Span of the whole declaration.
    pub span: Span,
}

/// `fact [name] { body }`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FactDecl {
    /// Optional fact name (identifier or string literal).
    pub name: Option<ParaName>,
    /// Body formula.
    pub body: ExprId,
    /// Span of the whole paragraph.
    pub span: Span,
}

/// `[private] pred [Receiver.]name [params] { body }`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PredDecl {
    /// Predicate name.
    pub name: Ident,
    /// Receiver sugar (`pred A.p[..]` — an implicit first param of type `A`).
    pub receiver: Option<QualName>,
    /// Parameters.
    pub params: Vec<DeclId>,
    /// Body formula.
    pub body: ExprId,
    /// `private` marker.
    pub is_private: bool,
    /// Span of the whole paragraph.
    pub span: Span,
}

/// `[private] fun [Receiver.]name [params] : returns { body }`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FunDecl {
    /// Function name.
    pub name: Ident,
    /// Receiver sugar (`fun A.f[..]`).
    pub receiver: Option<QualName>,
    /// Parameters.
    pub params: Vec<DeclId>,
    /// Declared result bound (with multiplicity marker if written).
    pub returns: ExprId,
    /// Body expression.
    pub body: ExprId,
    /// `private` marker.
    pub is_private: bool,
    /// Span of the whole paragraph.
    pub span: Span,
}

/// `assert [name] { body }`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AssertDecl {
    /// Assertion name (needed to `check` it, but grammatically optional;
    /// may be a string literal, which no command can reference).
    pub name: Option<ParaName>,
    /// Body formula.
    pub body: ExprId,
    /// Span of the whole paragraph.
    pub span: Span,
}

/// Top-level macro: `[private] let name [params] (= expr | { body })`.
///
/// Parameters are plain names (no bounds). A block body is stored as a
/// [`ExprKind::Block`] expression; `= expr` bodies as the expression itself.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MacroDecl {
    /// Macro name.
    pub name: Ident,
    /// Parameter names (empty for `let m = e` and `let m [] = e` alike).
    pub params: Vec<Ident>,
    /// Macro body.
    pub body: ExprId,
    /// `private` marker.
    pub is_private: bool,
    /// Span of the whole paragraph.
    pub span: Span,
}

/// `[label:] run|check target [scope] [expect 0|1]`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CmdDecl {
    /// Optional `label:` prefix.
    pub label: Option<Ident>,
    /// `run` or `check`.
    pub kind: CmdKind,
    /// What to run/check.
    pub target: CmdTarget,
    /// `for ...` scope clause.
    pub scope: Option<Scope>,
    /// `expect 0|1` annotation.
    pub expect: Option<Expect>,
    /// Chained onto the previous command via `=>`/`implies` (rare,
    /// undocumented, but grammatical).
    pub is_followup: bool,
    /// Span of the whole paragraph.
    pub span: Span,
}

/// Command kind.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CmdKind {
    /// `run` — find an instance.
    Run,
    /// `check` — find a counterexample.
    Check,
}

/// Target of a command.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CmdTarget {
    /// A named pred (`run p`) or assert (`check a`).
    Name(QualName),
    /// An inline block: `run { ... }`.
    Block(ExprId),
}

/// `expect` annotation: the model author's asserted verdict.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Expect {
    /// `expect 1` — an instance must exist.
    Sat,
    /// `expect 0` — no instance may exist.
    Unsat,
    /// `expect N` for any other integer — accepted by the reference,
    /// no expectation is checked.
    Other(i32),
}

/// `for N [but entries] | for entries` scope clause. Trace-length scopes
/// (`for 1..10 steps`) are ordinary entries with [`ScopeTarget::Steps`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Scope {
    /// Overall default scope (`for 3`), absent in the `for 3 A, 4 B` form.
    pub default: Option<u32>,
    /// Per-target scopes (`but exactly 2 A, 4 int, 1..10 steps`).
    pub entries: Vec<TypeScope>,
    /// Span of the whole clause.
    pub span: Span,
}

/// One `[exactly] N[..M][:I] target` scope entry.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TypeScope {
    /// `exactly` marker.
    pub is_exact: bool,
    /// Starting scope bound.
    pub start: u32,
    /// End of the bound range.
    pub end: ScopeEnd,
    /// `:I` growth increment, if written.
    pub increment: Option<u32>,
    /// What it bounds.
    pub target: ScopeTarget,
    /// Span of the entry.
    pub span: Span,
}

/// The range form of a [`TypeScope`] bound.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ScopeEnd {
    /// `N` — no range written.
    Same,
    /// `N..M`.
    Bounded(u32),
    /// `N..` — unbounded growth.
    Unbounded,
}

/// The subject of a [`TypeScope`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ScopeTarget {
    /// A sig reference.
    Sig(QualName),
    /// `int`/`Int` — bitwidth.
    Int,
    /// `seq` — maximum sequence length.
    Seq,
    /// `String` — string-atom scope.
    Str,
    /// `steps` — trace length (Alloy 6).
    Steps,
}

/// An expression (or formula — surface syntax does not distinguish).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Expr {
    /// What kind of node this is.
    pub kind: ExprKind,
    /// Where it was written (required, STYLE G1).
    pub span: Span,
}

/// Expression node kinds.
///
/// Core enums take no catch-all `_` in matches (`PORTING_RULES` R1): adding a
/// variant must surface every consumer that needs updating.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExprKind {
    /// Integer literal.
    Num(i32),
    /// String literal (interacts with the built-in `String` sig).
    Str(String),
    /// Built-in constant.
    Const(Const),
    /// `this` (inside sig facts and receivers).
    This,
    /// A (possibly qualified) name reference. Also carries builtin names the
    /// grammar spells with keywords (`univ`-as-sigref is [`Const`], but
    /// `Int`, `String`, `steps`, `seq/Int`, `disj`, `pred/totalOrder`,
    /// `int`/`sum` as call targets, and `fun/min|max|next` are synthesized
    /// `Name`s with exactly that text; resolution keys on it).
    Name(QualName),
    /// `@name` — suppresses the implicit `this.` expansion in sig facts.
    AtName(QualName),
    /// Prefix/postfix unary operation.
    Unary {
        /// Operator.
        op: UnOp,
        /// Operand.
        expr: ExprId,
    },
    /// Binary operation (everything except arrows and comparisons).
    Binary {
        /// Operator.
        op: BinOp,
        /// Left operand.
        lhs: ExprId,
        /// Right operand.
        rhs: ExprId,
    },
    /// Arrow product with optional multiplicities: `A m -> n B`.
    Arrow {
        /// Left operand.
        lhs: ExprId,
        /// Multiplicity on the left of `->`.
        lhs_mult: Option<Mult>,
        /// Multiplicity on the right of `->`.
        rhs_mult: Option<Mult>,
        /// Right operand.
        rhs: ExprId,
    },
    /// Comparison, possibly negated: `a !in b`, `x != y`.
    Compare {
        /// Comparison operator.
        op: CmpOp,
        /// `!`/`not` prefix on the operator.
        negated: bool,
        /// Left operand.
        lhs: ExprId,
        /// Right operand.
        rhs: ExprId,
    },
    /// `cond implies then else other` / `cond => then else other`.
    IfThenElse {
        /// Condition formula.
        cond: ExprId,
        /// Value/formula when true.
        then_branch: ExprId,
        /// Value/formula when false.
        else_branch: ExprId,
    },
    /// Box join / call: `f[x, y]` (also `x.f[y]` after the `.` parses as
    /// join). Whether this is a pred/fun call or a relational join is decided
    /// during resolution, not in the grammar.
    BoxJoin {
        /// The expression being applied.
        target: ExprId,
        /// Arguments in source order.
        args: Vec<ExprId>,
    },
    /// Quantified formula: `all disj x, y: A | body`, `sum x: A | body`.
    Quant {
        /// Quantifier.
        quant: Quant,
        /// Bindings.
        decls: Vec<DeclId>,
        /// Body.
        body: ExprId,
    },
    /// Set comprehension: `{ x: A, y: B | body }`.
    Comprehension {
        /// Bindings.
        decls: Vec<DeclId>,
        /// Membership condition.
        body: ExprId,
    },
    /// `let x = e, y = f | body`.
    Let {
        /// Bindings in source order (later bindings see earlier ones).
        bindings: Vec<LetBinding>,
        /// Body.
        body: ExprId,
    },
    /// `{ f1 f2 ... }` — block of formulas, conjoined.
    Block(Vec<ExprId>),
}

/// Built-in constant expressions.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Const {
    /// `none` — the empty unary relation.
    None,
    /// `univ` — the universe of atoms.
    Univ,
    /// `iden` — the binary identity relation.
    Iden,
}

/// One `name = value` binding in a `let`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LetBinding {
    /// Bound name.
    pub name: Ident,
    /// Bound value.
    pub value: ExprId,
    /// Span of the binding.
    pub span: Span,
}

/// Quantifiers (including `sum`, whose body is an integer expression).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Quant {
    /// `all`.
    All,
    /// `some`.
    Some,
    /// `no`.
    No,
    /// `lone`.
    Lone,
    /// `one`.
    One,
    /// `sum` — integer summation.
    Sum,
}

/// Multiplicity keywords (arrow annotations and declaration bounds).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Mult {
    /// `lone`.
    Lone,
    /// `one`.
    One,
    /// `some`.
    Some,
    /// `set`.
    Set,
}

/// Unary operators.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UnOp {
    // Formula prefixes.
    /// `!` / `not`.
    Not,
    /// `no e` — emptiness test.
    No,
    /// `some e` — non-emptiness test.
    Some,
    /// `lone e` — at-most-one test.
    Lone,
    /// `one e` — exactly-one test.
    One,
    // Multiplicity markers in declaration-bound position (`x: one A`,
    // `f: set A`, `s: seq A`). The parser picks these over the formula
    // prefixes by context; they desugar during resolution.
    /// `set` bound marker.
    SetOf,
    /// `some` bound marker.
    SomeOf,
    /// `lone` bound marker.
    LoneOf,
    /// `one` bound marker.
    OneOf,
    /// `seq` bound marker.
    SeqOf,
    // Relational.
    /// `~e` — transpose.
    Transpose,
    /// `^e` — transitive closure.
    Closure,
    /// `*e` — reflexive-transitive closure.
    ReflexiveClosure,
    /// `= e` defined-decl marker (defined fields); decl bounds only.
    ExactlyOf,
    // Integer.
    /// `#e` — cardinality.
    Card,
    /// `int e` — the summed integer value of `e`'s `Int` atoms.
    IntOf,
    /// `sum e` — same operation, `sum` spelling (distinct node for
    /// round-trip fidelity; `sum x: A | ie` is [`Quant`] instead).
    SumOf,
    // Temporal (Alloy 6), future and past.
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
    /// `e'` — the value of `e` in the next state (postfix prime).
    Prime,
}

/// Binary operators (arrows and comparisons have dedicated node kinds).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BinOp {
    // Logical.
    /// `||` / `or`.
    Or,
    /// `&&` / `and`.
    And,
    /// `<=>` / `iff`.
    Iff,
    /// `=>` / `implies` (without `else`).
    Implies,
    // Temporal (Alloy 6).
    /// `until`.
    Until,
    /// `releases`.
    Releases,
    /// `since`.
    Since,
    /// `triggered`.
    Triggered,
    /// `;` — sequential composition of formulas (sugar for `and after`).
    Seq,
    // Relational.
    /// `.` — relational join.
    Join,
    /// `+` — union.
    Union,
    /// `-` — difference.
    Diff,
    /// `&` — intersection.
    Intersect,
    /// `++` — override.
    Override,
    /// `<:` — domain restriction.
    DomRestrict,
    /// `:>` — range restriction.
    RanRestrict,
    // Integer.
    /// `<<` — shift left.
    Shl,
    /// `>>` — sign-extending shift right.
    Sha,
    /// `>>>` — zero-extending shift right.
    Shr,
    /// `fun/add` — integer addition.
    IntAdd,
    /// `fun/sub` — integer subtraction.
    IntSub,
    /// `fun/mul` — integer multiplication.
    IntMul,
    /// `fun/div` — integer division.
    IntDiv,
    /// `fun/rem` — integer remainder.
    IntRem,
}

/// Comparison operators (each may carry a `!`/`not` prefix, see
/// [`ExprKind::Compare`]).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CmpOp {
    /// `=`.
    Eq,
    /// `in` — subset.
    In,
    /// `<`.
    Lt,
    /// `>`.
    Gt,
    /// `=<` (also written `<=`).
    Le,
    /// `>=`.
    Ge,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ArenaId, FileId};

    fn span() -> Span {
        Span::new(FileId::from_index(0), 0, 1)
    }

    /// Builds `some x: A | x in A` by hand; pins the arena-construction shape.
    #[test]
    fn build_small_formula() {
        let mut ast = Ast::default();
        let name_a = QualName {
            segments: vec![Ident {
                text: "A".to_owned(),
                span: span(),
            }],
            span: span(),
        };
        let a_ref = ast.exprs.alloc(Expr {
            kind: ExprKind::Name(name_a.clone()),
            span: span(),
        });
        let x_ref = ast.exprs.alloc(Expr {
            kind: ExprKind::Name(QualName {
                segments: vec![Ident {
                    text: "x".to_owned(),
                    span: span(),
                }],
                span: span(),
            }),
            span: span(),
        });
        let body = ast.exprs.alloc(Expr {
            kind: ExprKind::Compare {
                op: CmpOp::In,
                negated: false,
                lhs: x_ref,
                rhs: a_ref,
            },
            span: span(),
        });
        let bound = ast.exprs.alloc(Expr {
            kind: ExprKind::Name(name_a),
            span: span(),
        });
        let decl = ast.decls.alloc(Decl {
            is_disj: false,
            is_bound_disj: false,
            is_var: false,
            is_private: false,
            names: vec![Ident {
                text: "x".to_owned(),
                span: span(),
            }],
            bound,
            span: span(),
        });
        let quant = ast.exprs.alloc(Expr {
            kind: ExprKind::Quant {
                quant: Quant::Some,
                decls: vec![decl],
                body,
            },
            span: span(),
        });

        let ExprKind::Quant {
            quant: q,
            decls,
            body,
        } = &ast.exprs[quant].kind
        else {
            panic!("expected quantifier node");
        };
        assert_eq!(*q, Quant::Some);
        assert_eq!(decls.len(), 1);
        assert!(matches!(
            ast.exprs[*body].kind,
            ExprKind::Compare {
                op: CmpOp::In,
                negated: false,
                ..
            }
        ));
    }
}
