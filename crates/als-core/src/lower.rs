//! IR lowering + goal assembly: the third translation phase (mt-031,
//! translation-ref §2). [`lower_command`] turns the resolved, type-checked
//! surface AST of one command into the single three-sorted-IR goal
//! ([`crate::ir`]) that the CNF encoder (mt-033) and solver (mt-032) consume.
//!
//! **Semantics faithful, structure idiomatic** (PORTING prime directive): a
//! bottom-up walk over the surface [`als_syntax::ast::Expr`], dispatching every
//! name / join / call at the exact point the reference does — but it **never
//! re-derives §4.4 resolution**. The mt-025 checker already recorded, for every
//! name and application spine, what it chose ([`als_types::choice`]); the
//! lowerer replays those choices ([`als_types::ChoiceTable`]) so name binding,
//! overload choice, implicit-`this` insertion, and macro expansion are read, not
//! recomputed (they took two beads to get right — duplication is drift).
//!
//! ## The goal (translation-ref §2.5), conjoined in order
//! 1. the bounds builder's constraint formulas (sibling disjointness, subset
//!    containment, **sig size/multiplicity** — mt-030 owns these, so the lowerer
//!    never re-emits them);
//! 2. every reachable module's **facts**;
//! 3. **synthesized field facts** — each field's declaration multiplicity
//!    (`all this: S | one this.f and this.f in bound`), domain (`f.univ… in S`),
//!    and defined-field value (`all this: S | this.f = e`);
//! 4. **sig appended facts** (`sig A {…}{ φ }`, with `this` bound to `A`);
//! 5. the **command formula** — a `run` pred body (params existentially
//!    quantified), a `run`/`check` block as-is/negated, or a `check` assertion
//!    body negated.
//!
//! The reference's §2.5(4) reflexive `r = r` padding is **not** emitted here: it
//! is a Kodkod solving detail (keeping unreferenced relations alive), and mt-033
//! owns it — see the note there.
//!
//! ## Deferred, as **typed** errors (never a silent skip, never a wrong verdict)
//! - **Temporal** operators (`always`/`until`/`'`/`var`) lower faithfully into
//!   the IR temporal kinds but the command then reports
//!   [`TranslateError::TemporalUnsupported`] (bounded LTL→FOL is Rung 6).
//! - **String literals** → their singleton relation (the jar's `s2k` map,
//!   translation-ref §13, mt-045): `ExprKind::Str` looks up
//!   [`BoundsResult::string_denote`], the exact one-atom relation the bounds
//!   phase bound for that referenced literal.
//! - Exotic field multiplicity shapes, higher-order (lean) macros, and
//!   unhandled command-target shapes → [`TranslateError::LoweringUnsupported`].
//! - **Higher-order quantification that cannot be skolemized** (a HO decl at
//!   universal polarity, or nested under a universal) →
//!   [`TranslateError::HigherOrder`], matching the reference's
//!   `HigherOrderDeclException` (translation-ref §2.3/§10.6).
//! - **Skolemization** (translation-ref §2.3/§10.6, mt-038): first-order
//!   quantifiers are lowered directly (ADR-0011); a **higher-order** existential
//!   decl (`some r: set A`, `some f: A one -> one B`, a relation-valued run-pred
//!   param) that is not under a universal is replaced by a fresh **free skolem
//!   relation** minted into [`LoweredGoal::skolem_bounds`] — the only way to solve
//!   it, and what makes ringlead/firewire lowerable. Effective polarity is threaded
//!   as [`Pol`]; the sound upper of a skolem's bound is [`Lowerer::abstract_upper`].

// Pervasive, harmless stylistic lints in this walk: `e`/`a`/`b`/`l`/`r` are the
// domain-idiomatic names for expression ids and operands (STYLE N4); several
// `match` arms over distinct `ExprKind`/choice variants share a body (a sort
// classification), which is clearer left un-merged; `choice`/`sort_of` helpers
// read as methods though a couple do not touch `self`.
#![allow(
    clippy::many_single_char_names,
    clippy::match_same_arms,
    clippy::unused_self
)]

use std::collections::{BTreeMap, BTreeSet};

use als_syntax::ast::{
    Ast, BinOp, CmpOp, Const, Decl, ExprId, ExprKind, LetBinding, Mult, Quant, UnOp,
};
use als_syntax::{ArenaId, Span};
use als_types::choice::{BuiltinCall, BuiltinValue, ExprChoice, NameChoice, SpineChoice};
use als_types::{
    ChoiceTable, CmdTargetResolved, FieldId, ModuleGraph, ModuleId, ResolvedWorld, SigId,
};

use crate::bounds::{RelBound, Tuple, TupleSet};
use crate::bounds_builder::BoundsResult;
use crate::error::TranslateError;
use crate::ir::{
    CompDecl, Formula, FormulaId, FormulaKind, IntBinOp, IntCmpOp, IntExpr, IntExprId, IntExprKind,
    Ir, MultTest, Mutability, QuantKind, RelBinOp, RelCmpOp, RelConst, RelExpr, RelExprId,
    RelExprKind, RelId, RelUnOp, Relation, TemporalBinOp, TemporalUnOp, Var,
};
use crate::scope::ScopedUniverse;

/// The lowered command goal (mt-031) and its provenance-labeled top-level
/// conjuncts (bookkeeping for mt-033's CNF encoder and for debugging).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LoweredGoal {
    /// The single goal formula: the conjunction of every conjunct below.
    pub goal: FormulaId,
    /// The top-level conjuncts with provenance, in §2.5 order.
    pub conjuncts: Vec<GoalConjunct>,
    /// The **skolem relations** minted for higher-order existential decls
    /// (translation-ref §2.3/§10.6): each freshly-allocated [`RelId`] with its
    /// [`RelBound`] (lower `{}`, upper = the sound abstract upper of the decl's
    /// bound). The solve driver binds these into the [`crate::bounds::Bounds`]
    /// before allocating primaries, so the encoder / decoder / self-check treat a
    /// skolem exactly like any other bounded relation (zero downstream
    /// special-casing). Empty for a goal with no skolemizable HO decl. In `RelId`
    /// allocation order (source-walk order — deterministic, STYLE D1).
    ///
    /// **First-order** skolems (mt-047, translation-ref §15) land here too — a
    /// top-level effective-existential FO decl (`some x: A | …`, or the `all` of a
    /// `check`'s negated body) becomes a skolem *constant* relation exactly like a
    /// HO one. [`Self::has_higher_order_skolem`] tells the two apart.
    pub skolem_bounds: Vec<(RelId, RelBound)>,
    /// Whether any skolem in [`Self::skolem_bounds`] came from a genuinely
    /// **higher-order** decl (ranging over sub-relations, mt-038). A goal whose
    /// skolems are all *first-order* (mt-047) counts exactly, so it is not subject
    /// to the gauge's conservative HO-count skip.
    pub has_higher_order_skolem: bool,
    /// The `Int`/`seq/Int` builtin relation ids (copied from the bounds builder),
    /// so the evaluator's forbid-mode overflow classifier can recognize a
    /// bare-`Int` quantifier domain (translation-ref §10.7c) without re-deriving
    /// them. `None` when the model uses no integers.
    pub int_sig: Option<RelId>,
    pub seq_int_sig: Option<RelId>,
}

/// One top-level conjunct of the goal, with where it came from.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GoalConjunct {
    /// The conjunct formula.
    pub formula: FormulaId,
    /// Its origin (translation-ref §2.5).
    pub provenance: Provenance,
}

/// Where a top-level goal conjunct came from (translation-ref §2.5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Provenance {
    /// A bounds-builder constraint (sig disjointness/subset/size/mult, mt-030).
    BoundsConstraint,
    /// A reachable module fact.
    Fact,
    /// A phase-8 `$`-metamodel **emptiness fact** — `no sig$` / `no static$` /
    /// `no var$`, one per synthesized sig the metamodel left with no members
    /// (mt-107 P3 tail, [`als_types::MetaEmptyFact`]). The reference adds these
    /// with `addFact`, so they are genuine root-module facts; they carry their
    /// own label rather than [`Self::Fact`] because there is no source
    /// paragraph behind them and a self-check failure here means the synthesis
    /// disagreed with the bounds, not that the user wrote something false.
    MetaFact(SigId),
    /// A synthesized field fact (multiplicity / domain / defined value).
    FieldFact(FieldId),
    /// A synthesized field-group disjointness fact from a pre-colon `disj a, b:
    /// …` declaration on the owning sig (translation-ref §2.5).
    FieldDisjFact(SigId),
    /// A sig appended fact (`this` bound to the owning sig).
    AppendedFact(SigId),
    /// The command formula.
    Command,
}

/// Lowers command `command_index` into the shared [`Ir`], producing the goal
/// (translation-ref §2). Consumes mt-029's [`ScopedUniverse`] and mt-030's
/// [`BoundsResult`] (denotation seam + constraint formulas); reads the resolved
/// choices from `world.choices`.
///
/// # Errors
/// A [`TranslateError`] for a deferred construct (temporal / string / exotic
/// field shape / unhandled target) — never a wrong verdict.
pub fn lower_command(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    bounds: &BoundsResult,
    ir: &mut Ir,
    command_index: usize,
) -> Result<LoweredGoal, TranslateError> {
    // The bounds builder already consumed `scoped` into the denotation seam; the
    // lowerer keeps only the bitwidth, for `fun/min`/`fun/max` (which the jar
    // translates to the int constants `min`/`max` of the bitwidth — §12).
    let cmd_label = skolem_command_label(world, graph, command_index);
    let mut lowerer = Lowerer {
        world,
        graph,
        bounds,
        ir,
        binders: Vec::new(),
        inline_stack: Vec::new(),
        temporal: None,
        pol: Pol::asserted(),
        cmd_label,
        skolem_bounds: Vec::new(),
        has_higher_order_skolem: false,
        skolem_names: BTreeSet::new(),
        var_bound: BTreeMap::new(),
        bitwidth: scoped.bitwidth,
        strings_closed: true,
    };
    lowerer.lower(command_index, TemporalPosture::Defer)
}

/// Lowers command `command_index` **keeping** its temporal IR nodes instead of
/// deferring on them (mt-066): the input to
/// [`crate::temporal_lower::lower_temporal_command`], which then eliminates them
/// by the LTL-on-lasso translation at a fixed trace length.
///
/// Identical to [`lower_command`] in every other respect — same walk, same
/// choices, same skolemization rules (which already block under every temporal
/// operator, `Skolemizer.java:494-526`) — so the two share one implementation
/// and cannot drift.
///
/// # Errors
/// Every [`TranslateError`] [`lower_command`] returns **except**
/// [`TranslateError::TemporalUnsupported`], which is the whole point.
pub fn lower_command_keeping_temporal(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    scoped: &ScopedUniverse,
    bounds: &BoundsResult,
    ir: &mut Ir,
    command_index: usize,
) -> Result<LoweredGoal, TranslateError> {
    let cmd_label = skolem_command_label(world, graph, command_index);
    let mut lowerer = Lowerer {
        world,
        graph,
        bounds,
        ir,
        binders: Vec::new(),
        inline_stack: Vec::new(),
        temporal: None,
        pol: Pol::asserted(),
        cmd_label,
        skolem_bounds: Vec::new(),
        has_higher_order_skolem: false,
        skolem_names: BTreeSet::new(),
        var_bound: BTreeMap::new(),
        bitwidth: scoped.bitwidth,
        strings_closed: true,
    };
    lowerer.lower(command_index, TemporalPosture::Keep)
}

/// What [`Lowerer::lower`] does when the walk hit a temporal construct: the
/// static pipeline defers the whole command ([`TranslateError::TemporalUnsupported`]),
/// the Rung-6 path keeps the nodes for [`crate::temporal_lower`] to translate.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum TemporalPosture {
    Defer,
    Keep,
}

/// A lowered evaluator fragment (mt-062): which of the three IR sorts the input
/// turned out to be, and its root node. The sort is what decides the rendered
/// shape — `true`/`false`, a bare numeral, or a tuple set
/// (`docs/reference/alloy6-evaluator.md` §3).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum LoweredFragment {
    /// A formula: renders `true`/`false`.
    Formula(FormulaId),
    /// An expression whose Kodkod translation is an `IntExpression` (`#e`,
    /// `sum x: B | e`, a shift): renders as a bare numeral. `plus[3,4]`, a
    /// numeral literal and `int[e]` are **not** here — they translate to
    /// `Expression`s and render `{7}`/`{3}` (evaluator contract §3).
    Int(IntExprId),
    /// A relational expression: renders `{tuple, …}`.
    Rel(RelExprId),
}

/// Which top-level dispatch a fragment's **root** takes — the one place the
/// reference's two fragment consumers genuinely differ (mt-099).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum FragmentRoot {
    /// The evaluator console. `CompModule.parseOneExpressionFromString`
    /// re-resolves the parsed body against its own type
    /// (`scratchpad/src794/CompModule.java:988-990`), which re-wraps an
    /// `Expression`-translating root in `Int[·]`, and `A4Solution.eval` then
    /// renders bare only what came back an `IntExpression`
    /// (`scratchpad/src794/A4Solution.java:1064-1070`). See
    /// [`Lowerer::fragment_sort`].
    Evaluator,
    /// A `fun` body the instance writer evaluates directly (`A4SolutionWriter`
    /// builds the `Expr` itself and never goes through the evaluator's
    /// re-resolve), so the root takes the ordinary in-expression sort.
    Value,
}

/// One standalone fragment to lower against an already-solved command.
#[derive(Copy, Clone, Debug)]
pub struct FragmentInput<'a> {
    /// The module the fragment was resolved *as* (its names are in scope).
    pub module: ModuleId,
    /// The arena the fragment's ids index into (not a loaded file's).
    pub ast: &'a Ast,
    /// The fragment's own resolution choices.
    pub choices: &'a ChoiceTable,
    /// The expression to lower.
    pub expr: ExprId,
    /// The solved command's bitwidth (inherited, evaluator contract §2).
    pub bitwidth: u32,
    /// Names bound to already-lowered values — the solved instance's atom and
    /// skolem names (evaluator contract §0 step 6), which the resolver bound
    /// like lexical variables and the lowerer therefore looks up like ones.
    pub globals: &'a [(String, RelExprId)],
    /// Which dispatch the fragment's root takes.
    pub root: FragmentRoot,
}

/// Lowers one standalone evaluator fragment into `ir`, alongside (and after)
/// the command whose instance it will be evaluated against.
///
/// The `Ir` arenas are append-only, so this never disturbs the already-solved
/// command's nodes; nothing here is re-encoded, only evaluated.
/// **Skolemization is blocked outright** — the instance is already fixed, so a
/// skolem would be a free relation nothing ever assigned; blocking also turns a
/// higher-order decl into the typed [`TranslateError::HigherOrder`] the
/// reference's evaluator reports as "Higher-order quantification is not allowed
/// in the evaluator." (evaluator contract §0 step 10).
///
/// # Errors
/// A [`TranslateError`] for anything outside the lowerable slice — a temporal
/// operator, a higher-order decl, or a construct the command pipeline defers
/// the same way.
pub fn lower_fragment<'a>(
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    bounds: &'a BoundsResult,
    ir: &'a mut Ir,
    input: &FragmentInput<'a>,
) -> Result<LoweredFragment, TranslateError> {
    lower_fragment_with(world, graph, bounds, ir, input, TemporalPosture::Defer)
}

/// [`lower_fragment`] **keeping** the fragment's temporal IR nodes instead of
/// deferring on them (mt-068) — the evaluator's twin of
/// [`lower_command_keeping_temporal`].
///
/// Every one of the 11 temporal operators is legal evaluator input against a
/// solved trace (alloy6-temporal.md §(h), probe T-24), so a temporal command's
/// REPL lowers through here and then eliminates the kept nodes at the current
/// state with
/// [`eliminate_fragment_at_state`](crate::temporal_lower::eliminate_fragment_at_state).
/// A *static* command's REPL keeps [`lower_fragment`]'s typed defer: there is no
/// trace to evaluate `after` against.
///
/// # Errors
/// Every [`TranslateError`] [`lower_fragment`] returns **except**
/// [`TranslateError::TemporalUnsupported`], which is the whole point.
pub fn lower_fragment_keeping_temporal<'a>(
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    bounds: &'a BoundsResult,
    ir: &'a mut Ir,
    input: &FragmentInput<'a>,
) -> Result<LoweredFragment, TranslateError> {
    lower_fragment_with(world, graph, bounds, ir, input, TemporalPosture::Keep)
}

/// The one fragment-lowering implementation the two postures share, so they
/// cannot drift (the same reason `lower_command`/`lower_command_keeping_temporal`
/// share theirs).
fn lower_fragment_with<'a>(
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    bounds: &'a BoundsResult,
    ir: &'a mut Ir,
    input: &FragmentInput<'a>,
    posture: TemporalPosture,
) -> Result<LoweredFragment, TranslateError> {
    let mut lowerer = Lowerer {
        world,
        graph,
        bounds,
        ir,
        binders: input
            .globals
            .iter()
            .map(|(name, value)| (name.clone(), Binding::Expr(*value)))
            .collect(),
        inline_stack: Vec::new(),
        temporal: None,
        pol: Pol {
            positive: true,
            blocked: true,
        },
        cmd_label: String::new(),
        skolem_bounds: Vec::new(),
        has_higher_order_skolem: false,
        skolem_names: BTreeSet::new(),
        var_bound: BTreeMap::new(),
        bitwidth: input.bitwidth,
        strings_closed: false,
    };
    let ctx = Ctx {
        module: input.module,
        choices: input.choices,
        ast: Some(input.ast),
    };
    // The same three-way split `lower_command` applies inside a command body,
    // here applied to the fragment's root: the input *is* the expression.
    let sort = match input.root {
        FragmentRoot::Evaluator => lowerer.fragment_sort(ctx, input.expr),
        FragmentRoot::Value => lowerer.sort_of(ctx, input.expr),
    };
    let value = match sort {
        Sort::Formula => LoweredFragment::Formula(lowerer.lower_formula(ctx, input.expr)?),
        // `visit_int`, not `lower_int`: `A4Solution.eval` renders whatever
        // `visitThis` returned and never calls `cint`, so a `#` at the root
        // stays a cardinality — `#(0-8)` is 1, not −8 (mt-052), and
        // `let x = 3 | #x` is 1 (mt-099).
        Sort::Int => LoweredFragment::Int(lowerer.visit_int(ctx, input.expr)?),
        Sort::Rel => LoweredFragment::Rel(lowerer.lower_rel(ctx, input.expr)?),
    };
    if let (TemporalPosture::Defer, Some((op, span))) = (posture, lowerer.temporal) {
        return Err(TranslateError::TemporalUnsupported { op, span });
    }
    debug_assert!(
        lowerer.skolem_bounds.is_empty(),
        "a blocked-polarity fragment minted a skolem relation"
    );
    Ok(value)
}

/// The skolem-name label for a command (translation-ref §2.3/§10.6/§15, probes
/// T9/K1–K3): its explicit `label:` prefix; else the target name — the run
/// pred/fun's name (`run p` → `$p_…`), or the checked assertion's declared name
/// (`check NoEmpty` → `$NoEmpty_…`); else empty (an anonymous `run`/`check {…}`,
/// skolems fall back to `$<var>`). A `$` in the label makes the reference drop
/// the prefix, so mettle does too. The assert name is not stored on the resolved
/// command (a resolution-doc scope choice), so it is recovered from the AST the
/// same way [`crate::exec`]-style callers do.
fn skolem_command_label(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    command_index: usize,
) -> String {
    let Some(cmd) = world.commands.get(command_index) else {
        return String::new();
    };
    let label = match &cmd.label {
        Some(l) if !l.contains('$') => l.clone(),
        Some(_) => return String::new(),
        None => match &cmd.target {
            CmdTargetResolved::Named(funcs) => funcs
                .first()
                .map(|&f| world.funcs[f].name.clone())
                .unwrap_or_default(),
            CmdTargetResolved::Assert { body, module } => {
                assert_decl_name(graph, *module, *body).unwrap_or_default()
            }
            _ => String::new(),
        },
    };
    if label.contains('$') {
        return String::new();
    }
    label
}

/// Recovers a checked assertion's declared name by walking its module's AST back
/// to the `assert` whose body matches (the reverse of `als_types`'s `find_assert`).
/// `ResolvedCommand` never stores the name, so this is where the skolem label
/// recovers it from the [`ModuleGraph`].
fn assert_decl_name(graph: &ModuleGraph, module: ModuleId, body: ExprId) -> Option<String> {
    use als_syntax::ast::{Para, ParaName};
    let file = graph.modules[module].file;
    let ast = graph.files.file(file).ast_ref();
    for &pid in &ast.paragraphs {
        if let Para::Assert(a) = &ast.paras[pid] {
            if a.body == body {
                return match &a.name {
                    Some(ParaName::Ident(id)) => Some(id.text.clone()),
                    Some(ParaName::Str { value, .. }) => Some(value.clone()),
                    None => None,
                };
            }
        }
    }
    None
}

/// A lexical binding active during lowering: mirrors the checker's env so a
/// `NameChoice::Var` resolves to the right IR node (innermost-wins shadowing).
#[derive(Clone)]
enum Binding {
    /// A quantifier / comprehension / `sum` variable → an IR relation variable.
    Var(crate::ir::VarId),
    /// A `let` binding, a func/pred parameter, or a macro argument → the
    /// already-lowered value expression (substituted in place, the reference's
    /// inlining).
    Expr(RelExprId),
    /// A formula-valued `let` binding (Alloy allows a `let` to bind a boolean:
    /// `let p = some a | p …`), kept **unlowered** (translation-ref §10.6a,
    /// mt-056). The jar translates the RHS once and *places that Kodkod node at
    /// each use*, while Kodkod's `Skolemizer` is a separate later pass over the
    /// assembled tree — so the §10.6 connective rule is decided at the **use**,
    /// not at the binding. Lowering here instead froze the decision at the
    /// binding site and minted skolems the jar refuses.
    ///
    /// `depth` is the binder-stack height at the binding site. The RHS is
    /// re-lowered at each use under the use's ambient [`SkolemPolarity`] but
    /// with the stack truncated back to `depth`, so a binder that **shadows** a
    /// name the RHS mentions cannot capture it — the jar cannot suffer capture,
    /// having translated the RHS once, and probe m2 `c01` measures it (26, the
    /// outer-`x` reading, not 20).
    ///
    /// The binding-site [`Ctx`] is deliberately NOT stored: macro replay builds
    /// one borrowing a locally-cloned `MacroChoice`, so it cannot outlive the
    /// lowerer. A `let`'s uses are lexically inside its own body — same AST
    /// arena, same choice table — so the use site's context interprets `expr`
    /// identically. `module` is kept purely as a tripwire: if a use ever arrives
    /// under a different module's context the lookup defers typed instead of
    /// reading `expr` against the wrong table.
    Formula {
        expr: ExprId,
        module: ModuleId,
        depth: usize,
    },
    /// A callable (func/pred) passed to a higher-order macro by bare name (§3.7,
    /// mt-040): the parameter is invoked as `param[args]` in the body and inlined
    /// as the real call, never used as a relational value.
    Callable(als_types::CallableChoice),
}

/// A resolution context: the module the expression lives in and the choice
/// table to read (the world's top table, or a macro body's nested table).
#[derive(Copy, Clone)]
struct Ctx<'a> {
    module: ModuleId,
    choices: &'a ChoiceTable,
    /// The arena this context's `ExprId`s index into, when it is **not** the
    /// module's own loaded AST: an evaluator fragment parsed standalone
    /// (mt-062, [`lower_fragment`]). The fragment still lowers *as*
    /// [`Self::module`] — that is whose names its choices were recorded
    /// against — so only the arena is redirected.
    ast: Option<&'a Ast>,
}

/// The three sorts an expression can lower to (translation-ref §2), decided
/// from the recorded choices — never a re-derivation of the §4 type checker.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Sort {
    Formula,
    Int,
    Rel,
}

/// How an int-sorted operand becomes a relation in a comparison
/// ([`Lowerer::lower_rel_promote`]). The reference has two distinct routes to
/// the same `IntToExprCast` node and mt-127 measured that they differ:
///
/// - [`Promote::ToSet`] is `toSet(a, visitThis(a))` (`:719-725`), the
///   translator wrapping whatever it just built. No `toInt`, so a cardinality
///   stays a cardinality. This is what `=`/`!=` do (`:1285-1306`).
/// - [`Promote::Cast`] is a resolver-inserted `Int[·]` (`int->Int`,
///   CAST2SIGINT), which translates as `cint(sub).toExpression()` (`:888`) —
///   so the operand goes through `toInt` and its peephole. This is what
///   `in`/`!in` get, because the resolver casts both their operands before the
///   translator ever sees them.
///
/// The one cell that separates them: `#(Int[3]) = 3` is UNSAT (`1 = 3`) while
/// `#(Int[3]) in 3` is SAT (`3 in 3`).
#[derive(Copy, Clone, PartialEq, Eq)]
enum Promote {
    ToSet,
    Cast,
}

/// Which side of a join a peeled arrow-column leaf variable lands on
/// (translation-ref §2.1, §10.3 probes n1/n3/n6): the *right* column
/// (checking `rhs`'s shape, iterating `lhs`'s tuples) peels each leaf onto
/// the **left** of the accumulator, in the type's own left-to-right column
/// order; the *left* column (checking `lhs`'s shape, iterating `rhs`'s
/// tuples) peels onto the **right**, in reverse (rightmost column peeled
/// first). See [`Lowerer::arrow_column`]/[`Lowerer::arrow_join_leaves`].
#[derive(Copy, Clone)]
enum JoinDir {
    FromLeft,
    FromRight,
}

/// The skolemization polarity of the formula node currently being lowered
/// (translation-ref §2.3/§10.6). Threaded through [`Lowerer::lower_formula`] so a
/// higher-order existential decl can be recognized as *skolemizable* — an
/// effective existential (in the NNF of the whole goal) not in the scope of any
/// universal — without materializing the NNF.
#[derive(Copy, Clone)]
struct Pol {
    /// Whether this node appears **positively** in the goal (an even number of
    /// negations above it). Flipped by `not`, by an `implies` antecedent, and set
    /// `false` for a `check`'s negated command body before its lowering.
    positive: bool,
    /// Whether skolemization is **blocked** here regardless of polarity: set once
    /// we descend under an effective-**universal** quantifier (a skolem constant
    /// would have to become a skolem function, depth ≥ 1), into a non-monotone
    /// context (`iff`, an int/formula-ITE condition, a comprehension/`sum` body, a
    /// temporal body), **or into a connective the jar refuses to skolemize under**
    /// (mt-055): a positive `or`/`implies` and a negated `and` (incl. a negated
    /// multi-conjunct block). Kodkod's `Skolemizer` sets `skolemDepth = -1` for
    /// the whole subtree in exactly those cases
    /// (`visit(BinaryFormula)`: `IFF || (negated && AND) || (!negated && (OR ||
    /// IMPLIES))`; `visit(NaryFormula)`: same for the n-ary forms). Skolemizing
    /// there would be *sound* — the jar is merely conservative — but a skolem is
    /// an extra free relation, so it is observable in model counts and in the
    /// §16.3 SBP relation order. Translation-ref §10.6.
    blocked: bool,
}

impl Pol {
    /// The initial polarity of a top-level goal conjunct that is asserted
    /// directly (a fact, a `run` command body): positive, nothing blocked.
    fn asserted() -> Self {
        Pol {
            positive: true,
            blocked: false,
        }
    }
}

struct Lowerer<'a> {
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    bounds: &'a BoundsResult,
    ir: &'a mut Ir,
    /// Active lexical bindings (innermost last).
    binders: Vec<(String, Binding)>,
    /// Funcs/preds currently being inlined (recursion guard — the reference
    /// rejects recursive funcs/preds; mettle refuses rather than looping).
    inline_stack: Vec<FuncIdx>,
    /// The first temporal construct hit (deferred at the end, translation-ref
    /// §2.3): `(op, span)`.
    temporal: Option<(&'static str, Span)>,
    /// The current skolemization polarity (translation-ref §10.6). Saved and
    /// restored around every polarity-changing recursion; read at HO decl sites.
    pol: Pol,
    /// Skolem label for names: `$<cmd_label>_<var>` (T9). Empty ⇒ `$<var>`.
    cmd_label: String,
    /// Skolem relations minted this command, with their bounds (see
    /// [`LoweredGoal::skolem_bounds`]). In allocation (source-walk) order.
    skolem_bounds: Vec<(RelId, RelBound)>,
    /// Set once a genuinely **higher-order** decl is skolemized (mt-038); stays
    /// false for a goal whose skolems are all first-order (mt-047). See
    /// [`LoweredGoal::has_higher_order_skolem`].
    has_higher_order_skolem: bool,
    /// Skolem relation names already allocated this command, so a name collision
    /// (two decls `some x: A | …` and `some x: A | …` under one command) mints
    /// **distinct** relations with **distinct** names — the jar's `un.make("$"+n)`
    /// uniquification (translation-ref §15). The suffix scheme (`_2`, `_3`, …) is
    /// mettle-chosen and display-only; the verdict/count depend only on the
    /// relations being distinct, which they always are (distinct [`RelId`]s).
    skolem_names: BTreeSet<String>,
    /// Each bound variable's declared bound expression, for [`Self::abstract_upper`]
    /// (translation-ref §10.6): a skolem whose bound depends on an enclosing
    /// existential variable `t` (`some r: f[t] one -> one g[t] | …`) is still a
    /// constant skolem — its upper is the *`t`-independent* over-approximation
    /// `f[upper(T)]`, sound because `r ⊆ f[t] ⊆ f[upper(T)]` (join/product are
    /// monotone) and the membership constraint still ties `r` to the chosen `t`.
    /// Only populated for first-order vars (a skolem never sits under a universal,
    /// so every enclosing var referenced here is itself existential — the reorder
    /// `∃r∃t = ∃t∃r` that justifies the constant skolem holds).
    var_bound: BTreeMap<crate::ir::VarId, RelExprId>,
    /// The command's bitwidth (signed range `−2^{bw-1}..2^{bw-1}−1`), for
    /// `fun/min`/`fun/max` lowering (translation-ref §12).
    bitwidth: u32,
    /// Whether every string literal reachable from here is guaranteed to have a
    /// denotation — true when lowering a command (the bounds phase collected
    /// them all), false for an evaluator fragment (mt-062), whose input may
    /// name a literal the solved command never referenced.
    strings_closed: bool,
}

impl<'a> Lowerer<'a> {
    // =============================== driver ===============================

    fn lower(
        &mut self,
        command_index: usize,
        posture: TemporalPosture,
    ) -> Result<LoweredGoal, TranslateError> {
        let cmd = self.world.commands.get(command_index).ok_or_else(|| {
            TranslateError::LoweringUnsupported {
                what: "command index out of range".to_owned(),
                span: als_types_synthetic_span(),
            }
        })?;
        let mut conjuncts: Vec<GoalConjunct> = Vec::new();

        // 1. bounds-builder constraints (mt-030 owns sig size/mult/disjoint).
        for &f in &self.bounds.constraints {
            conjuncts.push(GoalConjunct {
                formula: f,
                provenance: Provenance::BoundsConstraint,
            });
        }

        // 2. every reachable module fact — asserted at the top level, so a
        // higher-order existential inside one is skolemizable (translation-ref
        // §10.6): positive polarity, nothing blocked.
        for fact in &self.world.facts {
            let ctx = self.ctx(fact.module);
            self.pol = Pol::asserted();
            let f = self.lower_formula(ctx, fact.body)?;
            conjuncts.push(GoalConjunct {
                formula: f,
                provenance: Provenance::Fact,
            });
        }

        // 2b. the phase-8 metamodel's emptiness facts. `resolveMeta` appends
        // these to the *root module's* fact list at synthesis time, so they sit
        // right after the ordinary module facts — and, like them, at asserted
        // polarity (they are ground, so nothing here can skolemize either way).
        // P1 recorded each as a `(name, sig)` pair meaning `no <sig>`; this
        // replays that, it does not re-derive which sigs are empty.
        for fact in self.meta_empty_facts() {
            let f = self.lower_meta_empty_fact(fact.sig)?;
            conjuncts.push(GoalConjunct {
                formula: f,
                provenance: Provenance::MetaFact(fact.sig),
            });
        }

        // 3. synthesized field facts. Each is `all this: owner | …`, so a
        // nested HO existential in a defined-field value is under a universal —
        // blocked from skolemization (translation-ref §10.6).
        self.pol = Pol {
            positive: true,
            blocked: true,
        };
        for (fid, field) in self.world.fields.iter() {
            if let Some(f) = self.lower_field_facts(fid)? {
                conjuncts.push(GoalConjunct {
                    formula: f,
                    provenance: Provenance::FieldFact(fid),
                });
            }
            let _ = field;
        }

        // 3b. field-group `disj` facts (the jar emits each right after its
        // owner sig's field facts; translation-ref §2.5).
        for (sig, s) in self.world.sigs.iter() {
            for group in &s.field_disj_groups {
                if let Some(f) = self.lower_field_disj_group(group, s.span)? {
                    conjuncts.push(GoalConjunct {
                        formula: f,
                        provenance: Provenance::FieldDisjFact(sig),
                    });
                }
            }
        }

        // 4. sig appended facts (`this` bound to the owning sig) — `all this: A |
        // φ`, so a nested HO existential is under a universal (blocked).
        self.pol = Pol {
            positive: true,
            blocked: true,
        };
        for (sig, s) in self.world.sigs.iter() {
            if let Some(body) = s.appended_fact {
                let f = self.lower_appended_fact(sig, s.module, body)?;
                conjuncts.push(GoalConjunct {
                    formula: f,
                    provenance: Provenance::AppendedFact(sig),
                });
            }
        }

        // 5. the command formula.
        let cmd_f = self.lower_command_formula(command_index)?;
        conjuncts.push(GoalConjunct {
            formula: cmd_f,
            provenance: Provenance::Command,
        });

        // Defer if any temporal operator was lowered (translation-ref §2.3) —
        // unless the caller is the Rung-6 temporal path, which consumes them.
        if let (TemporalPosture::Defer, Some((op, span))) = (posture, self.temporal) {
            return Err(TranslateError::TemporalUnsupported { op, span });
        }

        let goal = self.conjoin(conjuncts.iter().map(|c| c.formula).collect(), cmd.span);
        Ok(LoweredGoal {
            goal,
            conjuncts,
            skolem_bounds: std::mem::take(&mut self.skolem_bounds),
            has_higher_order_skolem: self.has_higher_order_skolem,
            int_sig: self.bounds.int_sig,
            seq_int_sig: self.bounds.seq_int_sig,
        })
    }

    /// The metamodel's recorded emptiness facts, in synthesis order
    /// (`sig$fact`, `static$fact`, `var$fact` — only those the synthesis
    /// actually minted). Empty when the `$` gate never fired.
    fn meta_empty_facts(&self) -> Vec<als_types::MetaEmptyFact> {
        self.world
            .meta
            .as_ref()
            .map(|m| m.empty_facts.clone())
            .unwrap_or_default()
    }

    /// One emptiness fact: `no <sig>`. The recorded shape is a `(name, sig)`
    /// pair whose meaning [`als_types::MetaEmptyFact`] states outright, so this
    /// is a replay of the record rather than a re-derivation of which sigs are
    /// empty — the synthesis alone decides that (`resolveMeta` `:2230-2237`).
    fn lower_meta_empty_fact(&mut self, sig: SigId) -> Result<FormulaId, TranslateError> {
        let span = self.world.sigs[sig].span;
        self.pol = Pol::asserted();
        let denote = self.sig_denote(sig, span)?;
        Ok(self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::No,
                expr: denote,
            },
            span,
        ))
    }

    /// Builds the command formula (translation-ref §2.5(3)).
    fn lower_command_formula(&mut self, command_index: usize) -> Result<FormulaId, TranslateError> {
        let cmd = &self.world.commands[command_index];
        let is_check = matches!(cmd.kind, als_syntax::ast::CmdKind::Check);
        let span = cmd.span;
        match cmd.target.clone() {
            CmdTargetResolved::Block { body, module } => {
                let ctx = self.ctx(module);
                // A `check {block}` negates the block, so the body lowers at
                // **negative** polarity (its HO universals are effective
                // existentials — translation-ref §10.6); a `run {block}` is
                // asserted directly (positive).
                self.pol = Pol {
                    positive: !is_check,
                    blocked: false,
                };
                let f = self.lower_formula(ctx, body)?;
                Ok(if is_check { self.not(f, span) } else { f })
            }
            CmdTargetResolved::Assert { body, module } => {
                // `check a`: the assertion body, negated (SAT = counterexample) —
                // so the body lowers at negative polarity.
                let ctx = self.ctx(module);
                self.pol = Pol {
                    positive: false,
                    blocked: false,
                };
                let f = self.lower_formula(ctx, body)?;
                Ok(self.not(f, span))
            }
            CmdTargetResolved::Named(funcs) => {
                if is_check {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "`check` on a named pred/fun".to_owned(),
                        span,
                    });
                }
                let &func = funcs
                    .first()
                    .ok_or_else(|| TranslateError::LoweringUnsupported {
                        what: "empty run target".to_owned(),
                        span,
                    })?;
                if funcs.len() > 1 {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "overloaded run target".to_owned(),
                        span,
                    });
                }
                // Existentially quantify the params over their bounds, then the
                // body (translation-ref §2.5(3)). A `run` on a **fun** quantifies
                // the params identically but IGNORES the body (§2.5(3a), mt-097
                // probes c3/c4, c7/c8): the jar asserts nothing about the fun's
                // result, so `run f` is satisfiable exactly when the parameter
                // declarations are.
                self.run_pred(func, span)
            }
            CmdTargetResolved::Unresolved => Err(TranslateError::LoweringUnsupported {
                what: "unresolved command target".to_owned(),
                span,
            }),
        }
    }

    /// `run p`: `some x1: B1, …, xn: Bn | body` — the pred's params existentially
    /// quantified over their declaration bounds (translation-ref §2.5(3)); each
    /// top-level existential (receiver + params) skolemizes at depth 0 (§15). A
    /// receiver param (`pred A.p`) ranges over its sig `A`.
    ///
    /// **`run f` on a FUN uses the same parameter quantification and drops the
    /// body** (§2.5(3a), mt-097): the jar asserts nothing about a fun's result,
    /// so the command is satisfiable exactly when the parameter declarations are.
    /// Jar-pinned by the pred/fun pair — a contradictory *pred* body is UNSAT
    /// (`p_false`) while an always-empty *fun* result is SAT (`f_empty`) — and
    /// the parameters' declared multiplicities are respected (`x: A`/`x: one A`
    /// at an empty scope UNSAT, `x: lone A`/`x: set A` SAT).
    #[allow(clippy::too_many_lines)]
    fn run_pred(&mut self, func: FuncIdx, span: Span) -> Result<FormulaId, TranslateError> {
        let module = self.world.funcs[func].module;
        let body = self.world.funcs[func].body;
        let ctx = self.ctx(module);
        let Some(para) = self.find_func_para(module, func) else {
            return Err(TranslateError::LoweringUnsupported {
                what: "run pred: declaration not found".to_owned(),
                span,
            });
        };
        let ast = self.ast(module);
        let (receiver, param_decls) = match &ast.paras[para] {
            als_syntax::ast::Para::Pred(p) => (p.receiver.clone(), p.params.clone()),
            als_syntax::ast::Para::Fun(f) => (f.receiver.clone(), f.params.clone()),
            _ => (None, Vec::new()),
        };
        let mut var_bounds: Vec<(crate::ir::VarId, RelExprId)> = Vec::new();
        let mut pushed = 0usize;
        // A run-pred param (and the receiver `this`) is a **top-level existential**
        // (positive polarity, nothing blocked) — skolemizable at depth 0
        // (translation-ref §10.6/§15). `skolem_constraints` collects every skolem's
        // membership/multiplicity conjunct; each param binds to its skolem relation.
        self.pol = Pol::asserted();
        let mut skolem_constraints: Vec<FormulaId> = Vec::new();
        // Receiver `this` over its sig — a first-order existential (`one this: S`),
        // skolemized like any other (mt-047).
        if let Some(recv) = receiver {
            let sig = self.world.funcs[func]
                .params
                .first()
                .map(|_| ())
                .and_then(|()| {
                    // The receiver sig is the type of param 0 (`this`); recover it via
                    // the receiver name lookup.
                    self.lookup_sig_by_name(module, &recv)
                });
            let Some(sig) = sig else {
                return Err(TranslateError::LoweringUnsupported {
                    what: "run pred: unresolved receiver sig".to_owned(),
                    span,
                });
            };
            let bound = self.sig_denote(sig, span)?;
            if let Some(upper) = self.abstract_upper(bound) {
                let x = self.fo_skolemize("this", bound, 1, upper, span, &mut skolem_constraints);
                self.binders.push(("this".to_owned(), Binding::Expr(x)));
            } else {
                let vid = self.ir.vars.alloc(Var {
                    name: "this".to_owned(),
                    arity: 1,
                    span,
                });
                var_bounds.push((vid, bound));
                self.var_bound.insert(vid, bound);
                self.binders.push(("this".to_owned(), Binding::Var(vid)));
            }
            pushed += 1;
        }
        // A param that is set-valued (an explicit `set`/`some`/`lone` marker) or
        // higher-arity (default `set`, the jar's free skolem relation) is minted as
        // a free relation with its membership/multiplicity constraint (mt-038,
        // probe T9f); a plain unary param (default `one`) is a first-order
        // existential, skolemized to a constant singleton relation (mt-047).
        for &d in &param_decls {
            let decl = ast.decls[d].clone();
            if decl.is_bound_disj {
                return Err(bound_disj_unpinned(ast.exprs[decl.bound].span));
            }
            let set_expr = self.lower_decl_bound_set(ctx, &decl)?;
            let arity =
                self.ir_arity(set_expr)
                    .ok_or_else(|| TranslateError::LoweringUnsupported {
                        what: "run pred param of unknown arity".to_owned(),
                        span,
                    })?;
            let bound_span = ast.exprs[decl.bound].span;
            let is_higher_order = arity >= 2 || self.decl_is_higher_order(ctx, decl.bound);
            if is_higher_order {
                self.has_higher_order_skolem = true;
            }
            // A first-order param skolemizes when its bound has a sound abstract
            // upper (nearly always — a param bound is a plain relation); otherwise
            // it stays an ordinary existential (pre-mt-047 count, correct verdict).
            let fo_upper = if is_higher_order {
                None
            } else {
                self.abstract_upper(set_expr)
            };
            for name in &decl.names {
                if is_higher_order {
                    let x = self.mint_skolem(ctx, &name.text, &decl, name.span)?;
                    skolem_constraints
                        .extend(self.skolem_decl_constraints(ctx, x, &decl, bound_span)?);
                    self.binders.push((name.text.clone(), Binding::Expr(x)));
                } else if let Some(upper) = fo_upper.clone() {
                    let x = self.fo_skolemize(
                        &name.text,
                        set_expr,
                        arity,
                        upper,
                        name.span,
                        &mut skolem_constraints,
                    );
                    self.binders.push((name.text.clone(), Binding::Expr(x)));
                } else {
                    // Un-boundable bound: an ordinary first-order existential.
                    let vid = self.ir.vars.alloc(Var {
                        name: name.text.clone(),
                        arity: 1,
                        span: name.span,
                    });
                    var_bounds.push((vid, set_expr));
                    self.var_bound.insert(vid, set_expr);
                    self.binders.push((name.text.clone(), Binding::Var(vid)));
                }
                pushed += 1;
            }
        }
        // A fun's body is an EXPRESSION, and the jar never constrains it — the
        // command is `some <params> | true` (mt-097 §2.5(3a)). A pred's body is
        // the formula it asserts.
        let body_f = if self.world.funcs[func].is_pred {
            self.lower_formula(ctx, body)
        } else {
            Ok(self.mk_formula(FormulaKind::Const(true), span))
        };
        for _ in 0..pushed {
            self.binders.pop();
        }
        // `∃ params. (skolem-constraints ∧ body)` — the skolem relations are free
        // (their existential is discharged by being real relations); the FO params
        // and the receiver wrap as `some` quantifiers.
        let mut acc = body_f?;
        if !skolem_constraints.is_empty() {
            skolem_constraints.push(acc);
            acc = self.mk_formula(FormulaKind::And(skolem_constraints), span);
        }
        for (vid, bound) in var_bounds.into_iter().rev() {
            acc = self.mk_formula(
                FormulaKind::Quant {
                    kind: QuantKind::Some,
                    var: vid,
                    bound,
                    body: acc,
                },
                span,
            );
        }
        Ok(acc)
    }

    /// Looks up the sig a (possibly qualified) receiver name denotes, in a
    /// module's scope, via the resolved sigs' qualified names.
    fn lookup_sig_by_name(
        &self,
        module: ModuleId,
        name: &als_syntax::ast::QualName,
    ) -> Option<SigId> {
        let bare = name.segments.last()?.text.clone();
        let _ = module;
        self.world
            .sigs
            .iter()
            .find(|(_, s)| s.name == bare && !s.is_builtin)
            .map(|(id, _)| id)
    }

    // ============================ field facts ============================

    /// Synthesizes a field's declaration facts (translation-ref §2.5): domain
    /// (`f.univ… in owner`), per-declaration multiplicity + bound membership
    /// (`all this: S | mult(this.f) and this.f in bound`), or, for a defined
    /// field, `all this: S | this.f = e`. Returns `None` when there is nothing to
    /// add (a field whose bounds fully pin it).
    fn lower_field_facts(&mut self, fid: FieldId) -> Result<Option<FormulaId>, TranslateError> {
        let field = self.world.fields[fid].clone();
        let owner = field.owner;
        let module = self.world.sigs[owner].module;
        let ctx = self.ctx(module);
        let span = field.span;
        let field_denote = *self.bounds.field_denote.get(&fid).ok_or_else(|| {
            TranslateError::LoweringUnsupported {
                what: format!("field `{}` has no denotation", field.name),
                span,
            }
        })?;
        let owner_denote = self.sig_denote(owner, span)?;

        // `this` ranges over the owner; `this.f` is the value.
        let this_var = self.ir.vars.alloc(Var {
            name: "this".to_owned(),
            arity: 1,
            span,
        });
        let this_expr = self.mk_rel(RelExprKind::Var(this_var), span);
        let this_f = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: this_expr,
                rhs: field_denote,
            },
            span,
        );

        let mut body_parts: Vec<FormulaId> = Vec::new();
        if field.is_defined {
            let rhs = self.defined_field_value(ctx, &field, this_var, span)?;
            body_parts.push(self.mk_formula(
                FormulaKind::RelCompare {
                    op: RelCmpOp::Equal,
                    lhs: this_f,
                    rhs,
                },
                span,
            ));
        } else {
            // Multiplicity + membership from the declaration bound shape.
            self.binders
                .push(("this".to_owned(), Binding::Var(this_var)));
            let mult = self.field_mult_constraint(ctx, this_f, field.bound, span);
            self.binders.pop();
            body_parts.extend(mult?);
            // A `seq X` field adds the per-owner contiguity fact (§14): the used
            // indices form a prefix from 0. Emitted inside the `all this: owner`
            // wrapper via `body_parts`, so it is genuinely per-owner (probe
            // mt046-contig: two owners with indices {0,1} and {1} → UNSAT).
            if matches!(
                self.ast(module).exprs[field.bound].kind,
                ExprKind::Unary {
                    op: UnOp::SeqOf,
                    ..
                }
            ) {
                if let Some(contig) = self.seq_contiguity(this_f, span)? {
                    body_parts.push(contig);
                }
            }
        }

        // `all this: owner | <body>` (only when there is a body).
        let quant = if body_parts.is_empty() {
            None
        } else {
            let body = self.conjoin(body_parts, span);
            Some(self.mk_formula(
                FormulaKind::Quant {
                    kind: QuantKind::All,
                    var: this_var,
                    bound: owner_denote,
                    body,
                },
                span,
            ))
        };

        let domain = self.field_domain_constraint(fid, field_denote, owner_denote, span);

        // A post-colon `disj` field bound (`f: disj e`) adds cross-atom value
        // disjointness: for distinct owner atoms `this != that`,
        // `no (this.f & that.f)` — uniform at any field arity/multiplicity
        // (translation-ref §10.3 L27–L28).
        let disj = if field.is_bound_disj {
            Some(self.field_bound_disj_fact(field.is_var, field_denote, owner_denote, span))
        } else {
            None
        };

        let mut parts: Vec<FormulaId> = [quant, domain, disj].into_iter().flatten().collect();
        match parts.len() {
            0 => Ok(None),
            1 => Ok(Some(parts.remove(0))),
            _ => Ok(Some(self.conjoin(parts, span))),
        }
    }

    /// The right-hand side of a defined field's `all this: S | this.f = <rhs>`
    /// fact. A user field (`f = e`) lowers `e` in a `this`-context; a
    /// synthesized `$`-metamodel relation reads [`als_types::MetaDef`] instead —
    /// it has no source AST, so its `bound` is a placeholder that must never be
    /// read (see [`als_types::ResolvedField::bound`]), and its value mentions no
    /// `this` at all: every meta sig is a `one` sig, so the defined value is a
    /// constant per owner.
    fn defined_field_value(
        &mut self,
        ctx: Ctx,
        field: &als_types::ResolvedField,
        this_var: crate::ir::VarId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        if let Some(def) = &field.meta_def {
            return self.meta_def_denote(def, span);
        }
        let value = unwrap_exactly(self.ast_of(ctx), field.bound).ok_or_else(|| {
            TranslateError::LoweringUnsupported {
                what: format!("defined field `{}` malformed bound", field.name),
                span,
            }
        })?;
        self.binders
            .push(("this".to_owned(), Binding::Var(this_var)));
        let e = self.lower_rel(ctx, value);
        self.binders.pop();
        e
    }

    /// The value a synthesized `$`-metamodel relation is defined as (mt-107 P3):
    /// the sig or field the meta atom reflects, or the union of the meta sigs
    /// the `fields`/`parent`/`subfields` relations collect. An **empty** union
    /// is `none` of arity 1, matching the reference's `ExprConstant.EMPTYNESS`
    /// value (its declared type keeps a `univ` right column — see
    /// [`als_types::MetaDef::MetaSigs`]).
    fn meta_def_denote(
        &mut self,
        def: &als_types::MetaDef,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        match def {
            als_types::MetaDef::Sig(s) => self.sig_denote(*s, span),
            als_types::MetaDef::Field(f) => {
                self.bounds.field_denote.get(f).copied().ok_or_else(|| {
                    TranslateError::LoweringUnsupported {
                        what: format!(
                            "meta field `{}` has no denotation",
                            self.world.fields[*f].name
                        ),
                        span,
                    }
                })
            }
            // Union in the recorded (reference insertion) order — the members
            // are a `Vec`, so the tree shape is deterministic (STYLE D1).
            als_types::MetaDef::MetaSigs(members) => {
                let mut acc: Option<RelExprId> = None;
                for &m in members {
                    let d = self.sig_denote(m, span)?;
                    acc = Some(match acc {
                        None => d,
                        Some(prev) => self.mk_rel(
                            RelExprKind::Binary {
                                op: RelBinOp::Union,
                                lhs: prev,
                                rhs: d,
                            },
                            span,
                        ),
                    });
                }
                Ok(match acc {
                    Some(r) => r,
                    None => self.none_of_arity(1, span),
                })
            }
        }
    }

    /// The post-colon-`disj` cross-atom value-disjointness fact (mt-040):
    /// `all this: owner | all that: owner | this != that implies no (this.f &
    /// that.f)` — distinct owner atoms map to disjoint field values (jar-verified
    /// `DumpK2`; `this.f`/`that.f` are the owner-joined value slices, so the shape
    /// is uniform across field arity and multiplicity). A `var` field wraps the
    /// `no` in `always`, matching the field-group-`disj` convention (§2.2 /
    /// [`Self::lower_field_disj_group`]); such a command defers temporal anyway.
    fn field_bound_disj_fact(
        &mut self,
        is_var: bool,
        field_denote: RelExprId,
        owner_denote: RelExprId,
        span: Span,
    ) -> FormulaId {
        let this_var = self.ir.vars.alloc(Var {
            name: "this".to_owned(),
            arity: 1,
            span,
        });
        let that_var = self.ir.vars.alloc(Var {
            name: "that".to_owned(),
            arity: 1,
            span,
        });
        let this_e = self.mk_rel(RelExprKind::Var(this_var), span);
        let that_e = self.mk_rel(RelExprKind::Var(that_var), span);
        let join = |s: &mut Self, atom: RelExprId| {
            s.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Join,
                    lhs: atom,
                    rhs: field_denote,
                },
                span,
            )
        };
        let this_f = join(self, this_e);
        let that_f = join(self, that_e);
        let inter = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Intersect,
                lhs: this_f,
                rhs: that_f,
            },
            span,
        );
        let mut no_f = self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::No,
                expr: inter,
            },
            span,
        );
        if is_var {
            self.mark_temporal("always", span);
            no_f = self.mk_formula(
                FormulaKind::TemporalUnary {
                    op: TemporalUnOp::Always,
                    body: no_f,
                },
                span,
            );
        }
        // `this != that`: negate the equality of the two owner variables.
        let eq = self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Equal,
                lhs: this_e,
                rhs: that_e,
            },
            span,
        );
        let neq = self.not(eq, span);
        let implies = self.mk_formula(
            FormulaKind::Implies {
                antecedent: neq,
                consequent: no_f,
            },
            span,
        );
        // `all that: owner | …` then `all this: owner | …`.
        let all_that = self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: that_var,
                bound: owner_denote,
                body: implies,
            },
            span,
        );
        self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: this_var,
                bound: owner_denote,
                body: all_that,
            },
            span,
        )
    }

    /// The field domain constraint `(f.univ…) in owner` — the field's first
    /// column lies in the owner (translation-ref §2.5, jar-verified). Arity =
    /// the field's full arity; join `univ` (arity-1) `arity-1` times to project
    /// to the first column. `None` for a unary field (a `one`-sig-stripped
    /// denotation carries no owner column to constrain).
    fn field_domain_constraint(
        &mut self,
        fid: FieldId,
        field_denote: RelExprId,
        owner_denote: RelExprId,
        span: Span,
    ) -> Option<FormulaId> {
        let arity = self.world.fields[fid].ty.arity().filter(|&a| a >= 2)?;
        let mut proj = field_denote;
        let univ = self.mk_rel(RelExprKind::Const(RelConst::Univ), span);
        for _ in 0..(arity - 1) {
            proj = self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Join,
                    lhs: proj,
                    rhs: univ,
                },
                span,
            );
        }
        Some(self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: proj,
                rhs: owner_denote,
            },
            span,
        ))
    }

    /// The pairwise-disjointness fact for a pre-colon `disj f0, f1, …: bound`
    /// field group (translation-ref §2.5, jar-verified probes p1–p4). The jar
    /// emits the **staged** form over the fields' full relations —
    /// `no (f0 & f1) and no ((f0+f1) & f2) and …` — one `no` per successive
    /// field against the union of all earlier ones. A **`var`** group is wrapped
    /// per-conjunct in `always` (probe p5), which marks the goal temporal so the
    /// whole command defers (§2.3) — never a silent drop. The resolver only
    /// records groups of ≥2 fields, but the guard keeps this total.
    fn lower_field_disj_group(
        &mut self,
        group: &[FieldId],
        span: Span,
    ) -> Result<Option<FormulaId>, TranslateError> {
        if group.len() < 2 {
            return Ok(None);
        }
        // A group is temporal iff its fields are `var` (they share one decl, so
        // the marker is uniform); mirror the jar's per-`no` `always` wrapping.
        let is_var = group.iter().any(|&f| self.world.fields[f].is_var);
        let mut denote: Vec<RelExprId> = Vec::with_capacity(group.len());
        for &f in group {
            denote.push(*self.bounds.field_denote.get(&f).ok_or_else(|| {
                TranslateError::LoweringUnsupported {
                    what: format!("field `{}` has no denotation", self.world.fields[f].name),
                    span,
                }
            })?);
        }

        let mut parts: Vec<FormulaId> = Vec::with_capacity(group.len() - 1);
        // `acc` accumulates the union of all earlier fields; each stage forbids
        // the next field from intersecting it.
        let mut acc = denote[0];
        for (i, &next) in denote.iter().enumerate().skip(1) {
            let inter = self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Intersect,
                    lhs: acc,
                    rhs: next,
                },
                span,
            );
            let mut no_f = self.mk_formula(
                FormulaKind::MultTest {
                    test: MultTest::No,
                    expr: inter,
                },
                span,
            );
            if is_var {
                self.mark_temporal("always", span);
                no_f = self.mk_formula(
                    FormulaKind::TemporalUnary {
                        op: TemporalUnOp::Always,
                        body: no_f,
                    },
                    span,
                );
            }
            parts.push(no_f);
            // No need to extend the union past the last stage.
            if i + 1 < denote.len() {
                acc = self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Union,
                        lhs: acc,
                        rhs: next,
                    },
                    span,
                );
            }
        }
        Ok(Some(self.conjoin(parts, span)))
    }

    /// The per-declaration field multiplicity + membership constraints on
    /// `this_f = this.f`, from the declaration bound expression `bound`
    /// (translation-ref §2.1/§2.5): a plain unary bound gets an implicit `one`;
    /// `set`/`some`/`lone`/`one` markers set the multiplicity; a single arrow
    /// `A m -> n B` adds per-column multiplicity quantifiers. Deeper/exotic
    /// shapes defer.
    fn field_mult_constraint(
        &mut self,
        ctx: Ctx,
        this_f: RelExprId,
        bound: ExprId,
        span: Span,
    ) -> Result<Vec<FormulaId>, TranslateError> {
        let ast = self.ast_of(ctx);
        match &ast.exprs[bound].kind {
            // Multiplicity markers on a unary/relation bound.
            ExprKind::Unary { op, expr } if is_mult_marker(*op) => {
                let inner = *expr;
                let rel = self.lower_rel(ctx, inner)?;
                let membership = self.mk_formula(
                    FormulaKind::RelCompare {
                        op: RelCmpOp::Subset,
                        lhs: this_f,
                        rhs: rel,
                    },
                    span,
                );
                let mut out = vec![membership];
                if let Some(test) = mult_of_marker(*op) {
                    out.push(self.mk_formula(FormulaKind::MultTest { test, expr: this_f }, span));
                }
                Ok(out)
            }
            // A `seq X` bound desugars to `seq/Int -> lone X` (translation-ref
            // §14, LEDGER-008): membership over `seq/Int -> X` plus the
            // per-index `lone` value column. Equivalent to
            // `arrow_value_constraint` for the fixed `set seq/Int -> lone X`
            // shape, spelled directly because `seq/Int` has no AST `ExprId` to
            // feed that helper. The contiguity fact is added separately at the
            // `lower_field_facts` level (it is field-decl-only).
            ExprKind::Unary {
                op: UnOp::SeqOf,
                expr,
            } => self.seq_arrow_constraints(ctx, this_f, *expr, span),
            // An arrow product (flat or nested) with (optional) per-level
            // column multiplicities.
            ExprKind::Arrow {
                lhs,
                lhs_mult,
                rhs_mult,
                rhs,
            } => self.arrow_value_constraint(
                ctx, this_f, *lhs, *lhs_mult, *rhs_mult, *rhs, span, &mut 0,
            ),
            // A plain relation bound: implicit `one` for a unary value.
            _ => {
                let rel = self.lower_rel(ctx, bound)?;
                let membership = self.mk_formula(
                    FormulaKind::RelCompare {
                        op: RelCmpOp::Subset,
                        lhs: this_f,
                        rhs: rel,
                    },
                    span,
                );
                let mut out = vec![membership];
                // Implicit `one` when the value is unary (arity of this.f == 1).
                if self.rel_value_arity(bound, ctx) == Some(1) {
                    out.push(self.mk_formula(
                        FormulaKind::MultTest {
                            test: MultTest::One,
                            expr: this_f,
                        },
                        span,
                    ));
                }
                Ok(out)
            }
        }
    }

    /// A relation-valued field bound's arrow constraint `A m -> n B`,
    /// generalizing the flat case to arbitrarily nested arrows (translation-
    /// ref §2.1 arrow row, §10.3 probes L4 + mt-039 n1-n7 — jar-verified
    /// 2026-07-17): membership `value in (lhs -> rhs)`, plus two per-column
    /// quantifiers — one over `lhs`'s tuples enforcing `rhs_mult`/`rhs`'s own
    /// shape on the joined-from-the-left remainder, one over `rhs`'s tuples
    /// enforcing `lhs_mult`/`lhs`'s own shape on the joined-from-the-right
    /// preimage. A side that is itself `ExprKind::Arrow` recurses fully
    /// (probe n1: `A -> (B one -> one C)`) rather than testing a single
    /// multiplicity — this reproduces the jar's nested per-column
    /// quantifiers exactly. `value` may be any relation expression of the
    /// arrow's total arity, not just `this.f`: a reusable seam for
    /// skolem-relation multiplicity constraints.
    ///
    /// `col` numbers the per-call fresh variables `_c0`, `_c1`, … in
    /// allocation order (starting at 0 for the top-level call, threaded
    /// through recursion) — matching the pre-existing flat-case naming
    /// exactly, so `golden_arrow_right_one_multiplicity` is unchanged.
    ///
    /// Per §10.3 divergence (e), a column that would assert nothing new (no
    /// multiplicity marker on that side, and the other side is not itself an
    /// arrow to recurse into) is omitted entirely — matching the flat case's
    /// existing, tested behavior of never emitting the jar's redundant
    /// per-column membership (always entailed by the top-level membership,
    /// at any recursion depth: a joined slice of a value known to lie in a
    /// flat product is trivially a subset of the corresponding sub-product).
    #[allow(clippy::too_many_arguments)]
    fn arrow_value_constraint(
        &mut self,
        ctx: Ctx,
        value: RelExprId,
        lhs: ExprId,
        lhs_mult: Option<Mult>,
        rhs_mult: Option<Mult>,
        rhs: ExprId,
        span: Span,
        col: &mut u32,
    ) -> Result<Vec<FormulaId>, TranslateError> {
        let lhs_rel = self.lower_rel_stripped(ctx, lhs)?;
        let rhs_rel = self.lower_rel_stripped(ctx, rhs)?;
        let product = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Product,
                lhs: lhs_rel,
                rhs: rhs_rel,
            },
            span,
        );
        let membership = self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: value,
                rhs: product,
            },
            span,
        );
        let mut out = vec![membership];
        // Right column: for each tuple of `lhs`, the joined-from-the-left
        // remainder must satisfy `rhs`'s shape.
        out.extend(self.arrow_column(
            ctx,
            value,
            lhs,
            JoinDir::FromLeft,
            rhs,
            rhs_mult,
            span,
            col,
        )?);
        // Left column: symmetric, over `rhs`'s tuples against `lhs`'s shape.
        out.extend(self.arrow_column(
            ctx,
            value,
            rhs,
            JoinDir::FromRight,
            lhs,
            lhs_mult,
            span,
            col,
        )?);
        Ok(out)
    }

    /// The `seq/Int -> lone X` constraints on a value `value` of a `seq X`
    /// bound (translation-ref §14, LEDGER-008): membership `value in seq/Int ->
    /// X` plus the per-index `lone` value column `all i: seq/Int | lone
    /// i.value`. This is exactly what [`Self::arrow_value_constraint`] emits for
    /// `set seq/Int -> lone X` (the left column is empty — `seq/Int` carries no
    /// mark and `X` is not an arrow), spelled directly because `seq/Int` is a
    /// builtin with no source `ExprId` to pass through that helper. Does **not**
    /// emit the contiguity fact — that is field-decl-only (the jar's
    /// `ISSEQ_ARROW_LONE` branch is field translation) and is added by the
    /// caller for field decls only.
    fn seq_arrow_constraints(
        &mut self,
        ctx: Ctx,
        value: RelExprId,
        inner: ExprId,
        span: Span,
    ) -> Result<Vec<FormulaId>, TranslateError> {
        let x_rel = self.lower_rel(ctx, inner)?;
        let seq_int = self.sig_denote(self.world.builtins.seq_int, span)?;
        // membership: `value in seq/Int -> X` — meaningful (not just the bound):
        // it pins the value column to the *actual* `X`, which may be a strict
        // subset of `X`'s atoms.
        let product = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Product,
                lhs: seq_int,
                rhs: x_rel,
            },
            span,
        );
        let membership = self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: value,
                rhs: product,
            },
            span,
        );
        // lone value column: `all i: seq/Int | lone i.value`.
        let idx_var = self.fresh_col_var(1, span, &mut 0);
        let idx_e = self.mk_rel(RelExprKind::Var(idx_var), span);
        let joined = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: idx_e,
                rhs: value,
            },
            span,
        );
        let lone = self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::Lone,
                expr: joined,
            },
            span,
        );
        let quant = self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: idx_var,
                bound: seq_int,
                body: lone,
            },
            span,
        );
        Ok(vec![membership, quant])
    }

    /// The per-owner **contiguity** fact for a `seq X` field (translation-ref
    /// §14, LEDGER-008; jar-verified PER-OWNER, probe mt046-contig): the used
    /// indices of `this.f` form a prefix from `0`. Projecting `this.f` to its
    /// index column `dom`,
    /// `dom − dom.(Int/next) ⊆ Int/zero` — the only used index without a used
    /// predecessor is `0`. Wrapped in the enclosing `all this: owner |` by the
    /// caller (so it is genuinely per-owner). `None` when there are no int atoms
    /// (bitwidth 0 ⇒ `seq/Int` empty ⇒ the field is bound-empty and contiguity
    /// is vacuous).
    fn seq_contiguity(
        &mut self,
        this_f: RelExprId,
        span: Span,
    ) -> Result<Option<FormulaId>, TranslateError> {
        let (Some(next), Some(zero)) = (self.bounds.int_next, self.bounds.int_zero) else {
            return Ok(None);
        };
        let arity = self
            .ir_arity(this_f)
            .ok_or(TranslateError::HigherOrder { span })?;
        // dom = project `this.f` to its first (index) column: drop each value
        // column by joining `univ` on the right (same idiom as the field-domain
        // constraint).
        let mut dom = this_f;
        let univ = self.mk_rel(RelExprKind::Const(RelConst::Univ), span);
        for _ in 0..(arity - 1) {
            dom = self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Join,
                    lhs: dom,
                    rhs: univ,
                },
                span,
            );
        }
        // dom.(Int/next) = { i+1 : i ∈ dom } — the successors of used indices.
        let dom_next = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: dom,
                rhs: next,
            },
            span,
        );
        let diff = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Diff,
                lhs: dom,
                rhs: dom_next,
            },
            span,
        );
        Ok(Some(self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: diff,
                rhs: zero,
            },
            span,
        )))
    }

    /// One column of [`Self::arrow_value_constraint`]: quantify over `iter`'s
    /// tuples and, for each, constrain the `value`/tuple join (peeled per
    /// `dir`) against `other`'s shape via [`Self::arrow_check`]. A plain
    /// (non-`Arrow`) `iter` decl-binds one variable directly over its own
    /// denotation, of its own arity (Kodkod decl-binds any-arity relations
    /// with a single tuple variable) — this is the flat case. A compound
    /// (`Arrow`) `iter` has no single named relation to decl-bind, so it
    /// destructures into fresh `univ` leaf variables guarded by its own
    /// recursive constraint on the reconstructed tuple (probe n3: `(A -> B)
    /// one -> one C`'s left-nested column). Returns no formula when there is
    /// nothing to assert (divergence (e)) — checked *before* any variable is
    /// allocated, so a redundant column costs nothing.
    #[allow(clippy::too_many_arguments)]
    // `inner_lhs_mult`/`inner_rhs_mult` name the two sides of one destructured
    // Arrow decl (mirroring the arrow's own field names); renaming either
    // would obscure which is which.
    #[allow(clippy::similar_names)]
    fn arrow_column(
        &mut self,
        ctx: Ctx,
        value: RelExprId,
        iter: ExprId,
        dir: JoinDir,
        other: ExprId,
        other_mult: Option<Mult>,
        span: Span,
        col: &mut u32,
    ) -> Result<Vec<FormulaId>, TranslateError> {
        let other_is_arrow = matches!(&self.ast_of(ctx).exprs[other].kind, ExprKind::Arrow { .. });
        if mult_test_of(other_mult).is_none() && !other_is_arrow {
            return Ok(vec![]);
        }

        if matches!(&self.ast_of(ctx).exprs[iter].kind, ExprKind::Arrow { .. }) {
            let ExprKind::Arrow {
                lhs: inner_lhs,
                lhs_mult: inner_lhs_mult,
                rhs_mult: inner_rhs_mult,
                rhs: inner_rhs,
            } = self.ast_of(ctx).exprs[iter].kind.clone()
            else {
                unreachable!("just matched ExprKind::Arrow above");
            };
            let (leaves, recon) = self.arrow_leaf_vars(ctx, iter, span, col)?;
            let joined = self.arrow_join_leaves(value, &leaves, dir, span);
            let body = self.arrow_check(ctx, joined, other, other_mult, span, col)?;
            if body.is_empty() {
                return Ok(vec![]);
            }
            let guard_parts = self.arrow_value_constraint(
                ctx,
                recon,
                inner_lhs,
                inner_lhs_mult,
                inner_rhs_mult,
                inner_rhs,
                span,
                col,
            )?;
            let guard = self.conjoin(guard_parts, span);
            let body_f = self.conjoin(body, span);
            let implies = self.mk_formula(
                FormulaKind::Implies {
                    antecedent: guard,
                    consequent: body_f,
                },
                span,
            );
            let univ = self.mk_rel(RelExprKind::Const(RelConst::Univ), span);
            let mut acc = implies;
            for &v in leaves.iter().rev() {
                acc = self.mk_formula(
                    FormulaKind::Quant {
                        kind: QuantKind::All,
                        var: v,
                        bound: univ,
                        body: acc,
                    },
                    span,
                );
            }
            return Ok(vec![acc]);
        }

        let iter_rel = self.lower_rel(ctx, iter)?;
        let arity = self
            .ir_arity(iter_rel)
            .ok_or_else(|| TranslateError::LoweringUnsupported {
                what: "arrow operand of unknown arity".to_owned(),
                span,
            })?;
        let var = self.fresh_col_var(arity, span, col);
        let joined = self.arrow_join_leaves(value, std::slice::from_ref(&var), dir, span);
        let body = self.arrow_check(ctx, joined, other, other_mult, span, col)?;
        if body.is_empty() {
            return Ok(vec![]);
        }
        let body_f = self.conjoin(body, span);
        Ok(vec![self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var,
                bound: iter_rel,
                body: body_f,
            },
            span,
        )])
    }

    /// The multiplicity test and/or recursive structure `other` imposes on a
    /// joined value: a `MultTest` when `other_mult` is present, the full
    /// `arrow_value_constraint` when `other` is itself an arrow — both, if
    /// both apply (probe n7: `A -> some (B one -> one C)` marks the outer
    /// column AND recurses into the inner arrow simultaneously).
    fn arrow_check(
        &mut self,
        ctx: Ctx,
        joined: RelExprId,
        other: ExprId,
        other_mult: Option<Mult>,
        span: Span,
        col: &mut u32,
    ) -> Result<Vec<FormulaId>, TranslateError> {
        let mut out = Vec::new();
        if let Some(test) = mult_test_of(other_mult) {
            out.push(self.mk_formula(FormulaKind::MultTest { test, expr: joined }, span));
        }
        if let ExprKind::Arrow {
            lhs,
            lhs_mult,
            rhs_mult,
            rhs,
        } = self.ast_of(ctx).exprs[other].kind.clone()
        {
            out.extend(
                self.arrow_value_constraint(ctx, joined, lhs, lhs_mult, rhs_mult, rhs, span, col)?,
            );
        }
        Ok(out)
    }

    /// Allocates one fresh `univ`-bound variable per leaf (non-`Arrow`
    /// operand) of an arrow-shaped `expr`, plus the `RelExpr` reconstructing
    /// those leaves' product in the type's natural left-to-right column
    /// order (probes n1/n3/n6, §10.3): Kodkod decl-binds one variable
    /// directly over a *named* relation of any arity, but a literal nested
    /// arrow type has no such relation, so the jar destructures it leaf by
    /// leaf over `univ` instead.
    fn arrow_leaf_vars(
        &mut self,
        ctx: Ctx,
        expr: ExprId,
        span: Span,
        col: &mut u32,
    ) -> Result<(Vec<crate::ir::VarId>, RelExprId), TranslateError> {
        if let ExprKind::Arrow { lhs, rhs, .. } = self.ast_of(ctx).exprs[expr].kind.clone() {
            let (mut lvars, lrel) = self.arrow_leaf_vars(ctx, lhs, span, col)?;
            let (rvars, rrel) = self.arrow_leaf_vars(ctx, rhs, span, col)?;
            lvars.extend(rvars);
            let tuple = self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Product,
                    lhs: lrel,
                    rhs: rrel,
                },
                span,
            );
            Ok((lvars, tuple))
        } else {
            let rel = self.lower_rel(ctx, expr)?;
            let arity = self
                .ir_arity(rel)
                .ok_or_else(|| TranslateError::LoweringUnsupported {
                    what: "arrow operand of unknown arity".to_owned(),
                    span,
                })?;
            let var = self.fresh_col_var(arity, span, col);
            let var_e = self.mk_rel(RelExprKind::Var(var), span);
            Ok((vec![var], var_e))
        }
    }

    /// A fresh arrow-column variable, named `_cN` in allocation order.
    fn fresh_col_var(&mut self, arity: usize, span: Span, col: &mut u32) -> crate::ir::VarId {
        let name = format!("_c{col}");
        *col += 1;
        self.ir.vars.alloc(Var { name, arity, span })
    }

    /// Peels a column's leaf variables off `value` one at a time (probes
    /// n1/n3/n6): `FromLeft` peels left-to-right, each leaf joining onto the
    /// current **left** (`leaf . acc`) — the right-column/`rhs`-checking
    /// idiom. `FromRight` peels right-to-left, each leaf joining onto the
    /// current **right** (`acc . leaf`) — the left-column/`lhs`-checking
    /// idiom. A single-leaf slice (the flat case) reduces to one join,
    /// matching the pre-existing `av.this_f` / `this_f.bve` shape exactly.
    fn arrow_join_leaves(
        &mut self,
        value: RelExprId,
        leaves: &[crate::ir::VarId],
        dir: JoinDir,
        span: Span,
    ) -> RelExprId {
        let mut acc = value;
        match dir {
            JoinDir::FromLeft => {
                for &v in leaves {
                    let var_e = self.mk_rel(RelExprKind::Var(v), span);
                    acc = self.mk_rel(
                        RelExprKind::Binary {
                            op: RelBinOp::Join,
                            lhs: var_e,
                            rhs: acc,
                        },
                        span,
                    );
                }
            }
            JoinDir::FromRight => {
                for &v in leaves.iter().rev() {
                    let var_e = self.mk_rel(RelExprKind::Var(v), span);
                    acc = self.mk_rel(
                        RelExprKind::Binary {
                            op: RelBinOp::Join,
                            lhs: acc,
                            rhs: var_e,
                        },
                        span,
                    );
                }
            }
        }
        acc
    }

    /// A sig appended fact `sig A {…}{ φ }` — `φ` with `this` bound to `A`
    /// (translation-ref §2.5, resolution §3.3). Unlike a field/module fact it is
    /// `all this: A | φ` (the appended block holds for every atom of `A`).
    fn lower_appended_fact(
        &mut self,
        sig: SigId,
        module: ModuleId,
        body: ExprId,
    ) -> Result<FormulaId, TranslateError> {
        let span = self.world.sigs[sig].span;
        let ctx = self.ctx(module);
        let sig_denote = self.sig_denote(sig, span)?;
        let this_var = self.ir.vars.alloc(Var {
            name: "this".to_owned(),
            arity: 1,
            span,
        });
        self.binders
            .push(("this".to_owned(), Binding::Var(this_var)));
        let inner = self.lower_formula(ctx, body);
        self.binders.pop();
        let inner = inner?;
        Ok(self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: this_var,
                bound: sig_denote,
                body: inner,
            },
            span,
        ))
    }

    // ============================ formulas ============================

    #[allow(clippy::too_many_lines)]
    fn lower_formula(&mut self, ctx: Ctx, e: ExprId) -> Result<FormulaId, TranslateError> {
        let node = self.ast_of(ctx).exprs[e].clone();
        let span = node.span;
        match node.kind {
            ExprKind::Block(exprs) => {
                // An Alloy block is an `ExprList(AND)`, which `getSingleFormula`
                // (`TranslateAlloyToKodkod.java:1035-1058`) folds into a binary
                // heap of **`BinaryFormula` ANDs** — so a *negated* block blocks
                // skolemization throughout, via `visit(BinaryFormula)`'s
                // `negated && AND` (mt-055, translation-ref §10.6). The carve-out
                // is `getSingleFormula`'s own short-circuit: `n == 1` returns the
                // conjunct with **no AND node built at all**, so a single-conjunct
                // block (an `assert` body reached through `check`) still
                // skolemizes — which is what keeps §10.4's pinned 561 correct.
                let saved = self.pol;
                if !saved.positive && exprs.len() >= 2 {
                    self.pol.blocked = true;
                }
                let mut parts = Vec::with_capacity(exprs.len());
                let mut err = None;
                for f in exprs {
                    match self.lower_formula(ctx, f) {
                        Ok(p) => parts.push(p),
                        Err(e) => {
                            err = Some(e);
                            break;
                        }
                    }
                }
                self.pol = saved;
                if let Some(e) = err {
                    return Err(e);
                }
                Ok(self.conjoin(parts, span))
            }
            ExprKind::Compare {
                op,
                negated,
                lhs,
                rhs,
            } => {
                let f = self.lower_compare(ctx, op, lhs, rhs, span)?;
                Ok(if negated { self.not(f, span) } else { f })
            }
            ExprKind::Unary { op, expr } => self.lower_unary_formula(ctx, op, expr, span),
            // A `.`-join in formula position is a pred call spine.
            ExprKind::Binary {
                op: BinOp::Join, ..
            } => self.lower_call_formula(ctx, e, span),
            ExprKind::Binary { op, lhs, rhs } => self.lower_binary_formula(ctx, op, lhs, rhs, span),
            ExprKind::Quant { quant, decls, body } => {
                // A phase-8 ground expansion replaced this binder outright
                // (mt-107 P3) — it is a fold, not a quantifier, so it never
                // reaches `lower_quant`.
                if let Some(ExprChoice::Meta(me)) = self.choice(ctx, e).cloned() {
                    return self.replay_meta_formula(ctx, &me, span);
                }
                self.lower_quant(ctx, quant, &decls, body, span)
            }
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                // A formula-valued ITE. mettle's own IR shape is
                // `(cond and then) or (not cond and else)`, but the **jar's** is
                // `c.implies(then) and c.not().implies(else)`
                // (`TranslateAlloyToKodkod.visit(ExprITE)`, `.java:776-783`), and
                // that is what decides skolemization: at positive polarity the
                // two children are positive `IMPLIES` nodes, at negative polarity
                // the parent is a negated `AND` — `skolemDepth = -1` either way
                // (mt-055, translation-ref §10.6). So the condition **and both
                // branches** are blocked, at either polarity; `cond` was already
                // blocked for the independent non-monotone reason.
                let saved = self.pol;
                self.pol.blocked = true;
                let c = self.lower_formula(ctx, cond);
                let t = self.lower_formula(ctx, then_branch);
                let el = self.lower_formula(ctx, else_branch);
                self.pol = saved;
                let c = c?;
                let t = t?;
                let el = el?;
                let nc = self.not(c, span);
                let a = self.mk_formula(FormulaKind::And(vec![c, t]), span);
                let b = self.mk_formula(FormulaKind::And(vec![nc, el]), span);
                Ok(self.mk_formula(FormulaKind::Or(vec![a, b]), span))
            }
            ExprKind::Let { bindings, body } => {
                let pushed = self.push_let_bindings(ctx, &bindings)?;
                let r = self.lower_formula(ctx, body);
                for _ in 0..pushed {
                    self.binders.pop();
                }
                r
            }
            // A spine / name that resolves to a pred call or a 0-ary pred.
            ExprKind::BoxJoin { .. } | ExprKind::Name(_) | ExprKind::AtName(_) => {
                self.lower_call_formula(ctx, e, span)
            }
            ExprKind::This | ExprKind::Num(_) | ExprKind::Str(_) | ExprKind::Const(_) => {
                Err(TranslateError::LoweringUnsupported {
                    what: "non-formula in a formula position".to_owned(),
                    span,
                })
            }
            ExprKind::Arrow { .. } | ExprKind::Comprehension { .. } => {
                Err(TranslateError::LoweringUnsupported {
                    what: "non-formula expression in a formula position".to_owned(),
                    span,
                })
            }
        }
    }

    /// A name/spine in formula position: a 0-ary pred value or a pred call →
    /// inline the pred body; a builtin `disj[…]`/`pred/totalOrder[…]`.
    fn lower_call_formula(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        // A bare name resolving to a formula-valued `let` binding is that
        // formula (translation-ref §2): `let p = some a | p` uses `p` here.
        if let Some(ExprChoice::Name(NameChoice::Var(name))) = self.choice(ctx, e) {
            let name = name.clone();
            return self.lookup_binder_formula(ctx, &name, span);
        }
        // A higher-order-macro callable parameter applied as a formula
        // (`axiom[no_p]`, or bare `axiom`) inlines the recorded pred (mt-040).
        if let Some((c, args)) = self.callable_head(ctx, e) {
            if !c.is_pred {
                return Err(TranslateError::LoweringUnsupported {
                    what: "higher-order-macro function parameter in a formula position".to_owned(),
                    span,
                });
            }
            return self.inline_pred(ctx, c.func, &args, false, span);
        }
        match self.choice(ctx, e) {
            Some(ExprChoice::Name(NameChoice::Call0(func))) => {
                self.inline_pred(ctx, *func, &[], true, span)
            }
            Some(ExprChoice::Name(NameChoice::Macro(mc))) => {
                let mc = mc.clone();
                self.replay_macro_formula(ctx, &mc, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Call(cc))) => {
                let cc = cc.clone();
                self.inline_pred(ctx, cc.func, &cc.args, cc.implicit_this, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Builtin { op })) => {
                self.lower_builtin_formula(ctx, *op, e, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Macro(mc))) => {
                let mc = mc.clone();
                self.replay_macro_formula(ctx, &mc, span)
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "unrecognized formula-position spine".to_owned(),
                span,
            }),
        }
    }

    fn lower_unary_formula(
        &mut self,
        ctx: Ctx,
        op: UnOp,
        expr: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match op {
            UnOp::Not => {
                // `not` flips skolemization polarity (translation-ref §10.6).
                let saved = self.pol;
                self.pol.positive = !self.pol.positive;
                let f = self.lower_formula(ctx, expr);
                self.pol = saved;
                Ok(self.not(f?, span))
            }
            UnOp::No | UnOp::Some | UnOp::Lone | UnOp::One => {
                let r = self.lower_rel(ctx, expr)?;
                let test = match op {
                    UnOp::No => MultTest::No,
                    UnOp::Some => MultTest::Some,
                    UnOp::Lone => MultTest::Lone,
                    UnOp::One => MultTest::One,
                    _ => unreachable!(),
                };
                Ok(self.mk_formula(FormulaKind::MultTest { test, expr: r }, span))
            }
            UnOp::Always
            | UnOp::Eventually
            | UnOp::After
            | UnOp::Before
            | UnOp::Historically
            | UnOp::Once => {
                // A temporal body defers the whole command; block skolemization
                // within it (a skolem constant is not sound under `always`).
                let saved = self.pol;
                self.pol.blocked = true;
                let body = self.lower_formula(ctx, expr);
                self.pol = saved;
                let (kind, name) = temporal_un(op);
                self.mark_temporal(name, span);
                Ok(self.mk_formula(
                    FormulaKind::TemporalUnary {
                        op: kind,
                        body: body?,
                    },
                    span,
                ))
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "unary operator in a formula position".to_owned(),
                span,
            }),
        }
    }

    fn lower_binary_formula(
        &mut self,
        ctx: Ctx,
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match op {
            BinOp::And => {
                // Kodkod blocks skolemization under a **negated** `and`
                // (`Skolemizer.visit(BinaryFormula)`, mt-055 / §10.6).
                let saved = self.pol;
                if !saved.positive {
                    self.pol.blocked = true;
                }
                let l = self.lower_formula(ctx, lhs);
                let r = self.lower_formula(ctx, rhs);
                self.pol = saved;
                let (l, r) = (l?, r?);
                Ok(self.mk_formula(FormulaKind::And(vec![l, r]), span))
            }
            BinOp::Or => {
                // …and under a **positive** `or`, in both branches (§10.6). This
                // is the mt-055 rule: skolemizing here is sound but the jar does
                // not, and a skolem is an observable extra free relation.
                let saved = self.pol;
                if saved.positive {
                    self.pol.blocked = true;
                }
                let l = self.lower_formula(ctx, lhs);
                let r = self.lower_formula(ctx, rhs);
                self.pol = saved;
                let (l, r) = (l?, r?);
                Ok(self.mk_formula(FormulaKind::Or(vec![l, r]), span))
            }
            BinOp::Implies => {
                // `a implies b` ≡ `¬a ∨ b`: the antecedent flips polarity, the
                // consequent keeps it (translation-ref §10.6). A **positive**
                // implies blocks skolemization on both sides, like `or`; a
                // negated one does not (`!negated && IMPLIES` is the jar's test).
                let saved = self.pol;
                if saved.positive {
                    self.pol.blocked = true;
                }
                self.pol.positive = !saved.positive;
                let l = self.lower_formula(ctx, lhs);
                self.pol.positive = saved.positive;
                let r = self.lower_formula(ctx, rhs);
                self.pol = saved;
                let l = l?;
                let r = r?;
                Ok(self.mk_formula(
                    FormulaKind::Implies {
                        antecedent: l,
                        consequent: r,
                    },
                    span,
                ))
            }
            BinOp::Iff => {
                // Both sides appear in both polarities (non-monotone): block
                // skolemization within them.
                let saved = self.pol;
                self.pol.blocked = true;
                let l = self.lower_formula(ctx, lhs);
                let r = self.lower_formula(ctx, rhs);
                self.pol = saved;
                Ok(self.mk_formula(FormulaKind::Iff(l?, r?), span))
            }
            BinOp::Until | BinOp::Releases | BinOp::Since | BinOp::Triggered => {
                let saved = self.pol;
                self.pol.blocked = true;
                let l = self.lower_formula(ctx, lhs);
                let r = self.lower_formula(ctx, rhs);
                self.pol = saved;
                let (l, r) = (l?, r?);
                let (kind, name) = temporal_bin(op);
                self.mark_temporal(name, span);
                Ok(self.mk_formula(
                    FormulaKind::TemporalBinary {
                        op: kind,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
            BinOp::Seq => {
                // `a ; b` ≡ `a && after b` (grammar-ref §precedence level 1) —
                // not a primitive temporal connective. Still temporal (Rung 6).
                let l = self.lower_formula(ctx, lhs)?;
                let r = self.lower_formula(ctx, rhs)?;
                self.mark_temporal(";", span);
                let after = self.mk_formula(
                    FormulaKind::TemporalUnary {
                        op: TemporalUnOp::After,
                        body: r,
                    },
                    span,
                );
                Ok(self.mk_formula(FormulaKind::And(vec![l, after]), span))
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "binary operator in a formula position".to_owned(),
                span,
            }),
        }
    }

    fn lower_compare(
        &mut self,
        ctx: Ctx,
        op: CmpOp,
        lhs: ExprId,
        rhs: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match op {
            CmpOp::Lt | CmpOp::Gt | CmpOp::Le | CmpOp::Ge => {
                let l = self.lower_int(ctx, lhs)?;
                let r = self.lower_int(ctx, rhs)?;
                let iop = match op {
                    CmpOp::Lt => IntCmpOp::Lt,
                    CmpOp::Gt => IntCmpOp::Gt,
                    CmpOp::Le => IntCmpOp::Le,
                    CmpOp::Ge => IntCmpOp::Ge,
                    _ => unreachable!(),
                };
                Ok(self.mk_formula(
                    FormulaKind::IntCompare {
                        op: iop,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
            CmpOp::Eq | CmpOp::In => {
                // Integer special case (translation-ref §2.2, §10.7e FACT 1):
                // `=`/`!=` compare as integers iff BOTH translated sides are
                // literally `IntToExprCast`; `in`/`!in` never consult cast-ness
                // (`isIn`, :1327). That single test lives below, after the
                // promotion — there is no second, sort-level gate, because the
                // reference has none.
                //
                // The promotions differ, and mt-127 measured the difference.
                // `EQUALS` reaches its operands through `toSet(a, visitThis(a))`
                // (:1285-1306) — no `toInt`, so `#(Int[3]) = 3` is `1 = 3`,
                // UNSAT (probe a3). `IN` reaches them through `cset`, but the
                // resolver has already wrapped both int-typed operands in
                // `Int[·]` (`int->Int`, confirmed by an `AstDump` of the
                // resolved tree), and CAST2SIGINT is `cint(sub).toExpression()`
                // — so `#(Int[3]) in 3` IS `3 in 3`, SAT (probes a7/a8,
                // s7/s8 for `!in`).
                let l_int = self.sort_of(ctx, lhs) == Sort::Int;
                let r_int = self.sort_of(ctx, rhs) == Sort::Int;
                let promote = if matches!(op, CmpOp::Eq) {
                    Promote::ToSet
                } else {
                    Promote::Cast
                };
                // `x in A m -> n B`: the reference translates a
                // multiplicity-marked arrow on the `in` right-hand side as
                // membership over the stripped product PLUS the per-column
                // multiplicity constraints — the same conjunct set a field
                // decl of that shape produces (`isIn`; jar-verified via the
                // hotel2.als `Room<:keys in Room lone-> Key` fact, mt-037).
                // A marked arrow anywhere else (incl. an `=` side) falls
                // through to `lower_rel`'s typed defer.
                if matches!(op, CmpOp::In) && self.bound_is_higher_order(ctx, rhs) {
                    let ExprKind::Arrow {
                        lhs: alhs,
                        lhs_mult,
                        rhs_mult,
                        rhs: arhs,
                    } = self.ast_of(ctx).exprs[rhs].kind.clone()
                    else {
                        unreachable!("bound_is_higher_order is true only for ExprKind::Arrow");
                    };
                    let l = self.lower_rel_promote(ctx, lhs, l_int, promote)?;
                    let cs = self.arrow_value_constraint(
                        ctx, l, alhs, lhs_mult, rhs_mult, arhs, span, &mut 0,
                    )?;
                    return Ok(self.mk_formula(FormulaKind::And(cs), span));
                }
                let l = self.lower_rel_promote(ctx, lhs, l_int, promote)?;
                let r = self.lower_rel_promote(ctx, rhs, r_int, promote)?;
                // Both sides an `Int[·]` cast ⇒ an **integer** equality — the
                // reference's `eL instanceof IntToExprCast && eR instanceof
                // IntToExprCast` test, verbatim. It catches the promoted
                // int-sorted sides above AND an arithmetic result whose call
                // type is `Int` (`div[5,0] = div[5,0]`, where `sort_of` is
                // `Rel` and `lower_rel` produces the cast on its own).
                // Comparing the underlying ints keeps the forbid-mode overflow
                // guard (§11.3); the value is identical since distinct int
                // values map to distinct atoms.
                if matches!(op, CmpOp::Eq) {
                    if let (RelExprKind::IntToAtom(il), RelExprKind::IntToAtom(ir)) =
                        (&self.ir.rel_exprs[l].kind, &self.ir.rel_exprs[r].kind)
                    {
                        let (il, ir) = (*il, *ir);
                        return Ok(self.mk_formula(
                            FormulaKind::IntCompare {
                                op: IntCmpOp::Eq,
                                lhs: il,
                                rhs: ir,
                            },
                            span,
                        ));
                    }
                }
                let rop = if matches!(op, CmpOp::Eq) {
                    RelCmpOp::Equal
                } else {
                    RelCmpOp::Subset
                };
                Ok(self.mk_formula(
                    FormulaKind::RelCompare {
                        op: rop,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
        }
    }

    /// Lowers `e` as a relation, promoting a small-int value to its `Int` atom
    /// so it can be set-compared — in one of the two ways the reference does
    /// that, which are not interchangeable (see [`Promote`]).
    fn lower_rel_promote(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        is_int: bool,
        how: Promote,
    ) -> Result<RelExprId, TranslateError> {
        if is_int {
            let ie = match how {
                Promote::ToSet => self.visit_int(ctx, e)?,
                Promote::Cast => self.lower_int(ctx, e)?,
            };
            Ok(self.mk_rel(RelExprKind::IntToAtom(ie), self.span_of(ctx, e)))
        } else {
            self.lower_rel(ctx, e)
        }
    }

    // ============================ relations ============================

    #[allow(clippy::too_many_lines)]
    fn lower_rel(&mut self, ctx: Ctx, e: ExprId) -> Result<RelExprId, TranslateError> {
        let node = self.ast_of(ctx).exprs[e].clone();
        let span = node.span;
        // An int-sorted expression in relation position implicitly casts to its
        // `Int` atom (`Int[·]`, translation-ref §2.1's `IntToAtom` row) — the
        // symmetric counterpart of `lower_int`'s Rel->AtomToInt guard below.
        // Reachable whenever an Int-valued subexpression (`#e`, a call to an
        // Int-returning func, a `let`-bound int value) surfaces where a relation
        // is expected: a call argument (`bind_call_params` always lowers args via
        // `lower_rel`, regardless of the callee param's type), a `let` binding
        // value, or an operand of a genuinely relational `+`/`-`/`&` (jar-verified
        // probe p1, `scratchpad/probe/plus/p1.als`: `#A = #B + 1` lowers to
        // `Int[#A] = Int[#B] + Int[1]` — `+` stays relational **union** per
        // resolution §4.5's "no automatic int<->Int coercion" rule; only the
        // *operand* needs the cast, never the operator).
        //
        // This is `toSet` (`:719-725`), NOT a resolver-inserted `Int[·]`: the
        // reference wraps whatever `visitThis` returned, with no `toInt` on the
        // way in. So a union operand keeps its cardinality — `(#(Int[3]) +
        // Int[1]) = Int[1]` is SAT, probe z2 (mt-127). The positions where the
        // resolver *does* insert a cast, and the peephole therefore does fire,
        // ask for it explicitly: [`Self::lower_rel_promote`]'s `Promote::Cast`,
        // the `Int[·]` builtin arm, and `int[·]`/`sum`'s operand.
        if self.sort_of(ctx, e) == Sort::Int {
            let ie = self.visit_int(ctx, e)?;
            return Ok(self.mk_rel(RelExprKind::IntToAtom(ie), span));
        }
        match node.kind {
            ExprKind::Name(_) | ExprKind::AtName(_) => self.lower_name_rel(ctx, e, span),
            ExprKind::This => self.lower_this(span),
            // `univ`/`iden` in **user-expression** position denote the jar's
            // *live universe*, not the all-atoms constant (mt-053, LEDGER-011;
            // A4Solution.java:336–338/699 + TranslateAlloyToKodkod.java:824/893 @
            // `794226dd`; probe matrix `scratchpad/probe/mt053/NOTES.md`). The
            // all-atoms `RelConst::Univ`/`Iden` survive only for the encoder's
            // internal/bounds-level uses (field-domain projection, `<:`/`:>`
            // padding, seq contiguity, `abstract_upper`) — sound
            // over-approximations there, with liveness enforced by these live
            // membership expressions.
            ExprKind::Const(Const::None) => {
                Ok(self.mk_rel(RelExprKind::Const(RelConst::None), span))
            }
            ExprKind::Const(Const::Univ) => Ok(self.live_univ(span)),
            ExprKind::Const(Const::Iden) => Ok(self.live_iden(span)),
            ExprKind::Num(_) => {
                // A small-int in relation position → its `Int` atom. This IS
                // the reference's numeral arm verbatim: `visit(ExprConstant)`
                // case NUMBER is `IntConstant.constant(n).toExpression()`
                // (`:918`), i.e. an `IntToExprCast` — which is why a numeral
                // then-branch makes an if-then-else relational
                // ([`Self::ite_sort`]).
                let ie = self.visit_int(ctx, e)?;
                Ok(self.mk_rel(RelExprKind::IntToAtom(ie), span))
            }
            ExprKind::Str(s) => {
                // A string literal lowers to its singleton relation (the jar's
                // `s2k` map, translation-ref §13). Every literal reachable from
                // the goal was collected into the universe by
                // `strings::collect_referenced_literals` and given a denotation
                // in the bounds phase; a miss is an internal invariant
                // violation, never a silent empty relation (negative space).
                // An evaluator fragment (mt-062) is the one caller for which
                // that closure does NOT hold — a literal typed at the prompt
                // was never seen by the solved command, so it has no atom in
                // that command's universe. There it is an ordinary user error
                // (the reference: "String literal \"…\" does not exist in
                // this instance.", evaluator contract §3/E-49), not an
                // invariant violation.
                debug_assert!(
                    !self.strings_closed || self.bounds.string_denote.contains_key(&s),
                    "string literal {s:?} in the goal was not collected into the universe"
                );
                self.bounds.string_denote.get(&s).copied().ok_or_else(|| {
                    TranslateError::LoweringUnsupported {
                        what: format!("string literal {s:?} does not exist in this instance"),
                        span,
                    }
                })
            }
            ExprKind::Binary { op, lhs, rhs } => self.lower_binary_rel(ctx, e, op, lhs, rhs, span),
            ExprKind::BoxJoin { .. } => self.lower_spine_rel(ctx, e, span),
            ExprKind::Arrow { lhs, rhs, .. } => {
                // A multiplicity-marked arrow is only meaningful as a decl
                // bound or an `in` right-hand side (both handled by
                // [`Self::arrow_value_constraint`] callers). Anywhere else,
                // silently stripping the marks lowered `Room lone-> Key` to a
                // plain product and produced a wrong verdict (hotel2.als,
                // mt-037): defer typed instead (STYLE E5).
                if self.bound_is_higher_order(ctx, e) {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "multiplicity-marked arrow outside a declaration or `in` bound"
                            .to_owned(),
                        span,
                    });
                }
                let l = self.lower_rel(ctx, lhs)?;
                let r = self.lower_rel(ctx, rhs)?;
                Ok(self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Product,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
            ExprKind::Unary { op, expr } => self.lower_unary_rel(ctx, op, expr, span),
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let saved = self.pol;
                self.pol.blocked = true;
                let c = self.lower_formula(ctx, cond);
                self.pol = saved;
                let c = c?;
                let t = self.lower_rel(ctx, then_branch)?;
                let el = self.lower_rel(ctx, else_branch)?;
                Ok(self.mk_rel(
                    RelExprKind::IfThenElse {
                        cond: c,
                        then_branch: t,
                        else_branch: el,
                    },
                    span,
                ))
            }
            ExprKind::Comprehension { decls, body } => {
                // The comprehension arm of the same phase-8 expansion: a union
                // of guarded singletons, not a comprehension (mt-107 P3).
                if let Some(ExprChoice::Meta(me)) = self.choice(ctx, e).cloned() {
                    return self.replay_meta_rel(ctx, &me, span);
                }
                self.lower_comprehension(ctx, &decls, body, span)
            }
            ExprKind::Let { bindings, body } => {
                let pushed = self.push_let_bindings(ctx, &bindings)?;
                let r = self.lower_rel(ctx, body);
                for _ in 0..pushed {
                    self.binders.pop();
                }
                r
            }
            // A single-element block `{ e }` (e.g. a fun body) is just `e`.
            ExprKind::Block(exprs) if exprs.len() == 1 => self.lower_rel(ctx, exprs[0]),
            ExprKind::Block(_) | ExprKind::Quant { .. } | ExprKind::Compare { .. } => {
                Err(TranslateError::LoweringUnsupported {
                    what: "formula in a relation position".to_owned(),
                    span,
                })
            }
        }
    }

    fn lower_name_rel(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let choice = self.choice(ctx, e).cloned();
        match choice {
            Some(ExprChoice::Name(nc)) => self.lower_name_choice(ctx, &nc, span),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "name without a recorded resolution".to_owned(),
                span,
            }),
        }
    }

    fn lower_name_choice(
        &mut self,
        ctx: Ctx,
        nc: &NameChoice,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        match nc {
            NameChoice::Var(name) => self.lookup_binder(name, span),
            NameChoice::Sig(sig) => self.sig_denote(*sig, span),
            NameChoice::Field {
                field,
                implicit_this,
            } => {
                let fd = *self.bounds.field_denote.get(field).ok_or_else(|| {
                    TranslateError::LoweringUnsupported {
                        what: "field without a denotation".to_owned(),
                        span,
                    }
                })?;
                if *implicit_this {
                    let this = self.lookup_binder("this", span)?;
                    Ok(self.mk_rel(
                        RelExprKind::Binary {
                            op: RelBinOp::Join,
                            lhs: this,
                            rhs: fd,
                        },
                        span,
                    ))
                } else {
                    Ok(fd)
                }
            }
            NameChoice::Call0(func) => self.inline_fun(ctx, *func, &[], true, span),
            NameChoice::Builtin(bv) => self.lower_builtin_value(*bv, span),
            NameChoice::Macro(mc) => self.replay_macro_rel(ctx, mc, span),
            NameChoice::EmptyArity(k) => Ok(self.none_of_arity(*k, span)),
        }
    }

    /// Lowers a `util/integer` builtin value spelled by name (translation-ref
    /// §12): `fun/min`/`fun/max` become the int constants `min`/`max` of the
    /// bitwidth cast to `Int` atoms (`Int[c]`, matching the jar's
    /// `IntConstant.constant(min/max).toExpression()`); `fun/next` is the
    /// `Int/next` relation; `fun/prev` its transpose.
    fn lower_builtin_value(
        &mut self,
        bv: BuiltinValue,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        match bv {
            BuiltinValue::IntMin | BuiltinValue::IntMax => {
                let value = match bv {
                    BuiltinValue::IntMin => int_min(self.bitwidth),
                    _ => int_max(self.bitwidth),
                };
                let konst = self.mk_int(IntExprKind::Const(value), span);
                Ok(self.mk_rel(RelExprKind::IntToAtom(konst), span))
            }
            BuiltinValue::IntNext => {
                self.bounds
                    .int_next
                    .ok_or_else(|| TranslateError::LoweringUnsupported {
                        what: "`fun/next` with no integer atoms (bitwidth 0)".to_owned(),
                        span,
                    })
            }
            BuiltinValue::IntPrev => {
                let next =
                    self.bounds
                        .int_next
                        .ok_or_else(|| TranslateError::LoweringUnsupported {
                            what: "`fun/prev` with no integer atoms (bitwidth 0)".to_owned(),
                            span,
                        })?;
                Ok(self.mk_rel(
                    RelExprKind::Unary {
                        op: RelUnOp::Transpose,
                        expr: next,
                    },
                    span,
                ))
            }
        }
    }

    /// Whether `lhs op rhs` is the jar's one `MINUS` peephole: `0 - (max+1)`
    /// folds to the int constant `min` (translation-ref §10.7i;
    /// `TranslateAlloyToKodkod.java:1239-1248` @ `794226dd`; probe matrix
    /// `scratchpad/probe/mt052/NOTES.md`).
    ///
    /// It exists so the most-negative literal can be written at all: `-8` is
    /// not surface syntax, and `8` at bitwidth 4 is already out of range, so
    /// without the fold there would be no way to spell `min` without an
    /// out-of-range intermediate.
    ///
    /// The guard is **syntactic, on the resolved AST, and un-`deNOP`ed** —
    /// `visit(ExprBinary)` reads `x.left`/`x.right` raw and tests
    /// `instanceof ExprConstant` with `op == NUMBER`. So it survives
    /// parentheses (the parser folds those around a numeral without a wrapper
    /// node: cells C03–C05) but nothing else. Everything below stays plain set
    /// difference, and each is a pinned cell: an in-range right operand
    /// (`0-2`, C06 — the mt-044 `(0-1)` artifact family), a non-zero left one
    /// (`1-8`, C10), a right operand past `max+1` (`0-9`, C11), a *computed*
    /// `max+1` (`0-plus[4,4]`, C13 — value-based folding is explicitly not the
    /// rule), a `let`-bound one (`let k = 8 | 0-k`, E17/E18), and the same
    /// numeral at a bitwidth where it is not `max+1` (`0-8` at bw 5, C15).
    ///
    /// `min`/`max` are the *command's* (`A4Solution.java:161-162`), so the
    /// trigger literal moves with the scope: `0-1` at bw 1, `0-2` at bw 2,
    /// `0-4` at bw 3 (F01–F06, C16).
    ///
    /// Callers rely on the fold's result being an `IntExpression` rather than
    /// an `Expression`, which is why this is consulted from
    /// [`Self::sort_of`] — see the `BinOp::Diff` arm there for what that buys.
    fn minus_folds_to_min(&self, ctx: Ctx, op: BinOp, lhs: ExprId, rhs: ExprId) -> bool {
        if op != BinOp::Diff {
            return false;
        }
        let Some(trigger) = int_max(self.bitwidth).checked_add(1) else {
            return false;
        };
        let exprs = &self.ast_of(ctx).exprs;
        matches!(exprs[lhs].kind, ExprKind::Num(0))
            && matches!(exprs[rhs].kind, ExprKind::Num(n) if n == trigger)
    }

    fn lower_binary_rel(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let rel_op = match op {
            BinOp::Union => Some(RelBinOp::Union),
            BinOp::Diff => Some(RelBinOp::Diff),
            BinOp::Intersect => Some(RelBinOp::Intersect),
            BinOp::Override => Some(RelBinOp::Override),
            _ => None,
        };
        if let Some(rb) = rel_op {
            let l = self.lower_rel(ctx, lhs)?;
            let r = self.lower_rel(ctx, rhs)?;
            return Ok(self.mk_rel(
                RelExprKind::Binary {
                    op: rb,
                    lhs: l,
                    rhs: r,
                },
                span,
            ));
        }
        match op {
            BinOp::Join => self.lower_spine_rel(ctx, e, span),
            BinOp::DomRestrict => self.lower_restrict(ctx, lhs, rhs, true, span),
            BinOp::RanRestrict => self.lower_restrict(ctx, lhs, rhs, false, span),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "binary operator in a relation position".to_owned(),
                span,
            }),
        }
    }

    /// A `.`-join or box-join spine in relation position — dispatch on the
    /// recorded [`SpineChoice`] (join / fun call / `Int[·]` / macro).
    fn lower_spine_rel(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        // A higher-order-macro callable parameter applied as a relation
        // (`f[x]` where `f` is a function argument) inlines the recorded fun.
        if let Some((c, args)) = self.callable_head(ctx, e) {
            if c.is_pred {
                return Err(TranslateError::LoweringUnsupported {
                    what: "higher-order-macro predicate parameter in a relation position"
                        .to_owned(),
                    span,
                });
            }
            return self.inline_fun(ctx, c.func, &args, false, span);
        }
        let choice = self.choice(ctx, e).cloned();
        match choice {
            Some(ExprChoice::Spine(SpineChoice::Join)) => self.lower_join_structural(ctx, e, span),
            Some(ExprChoice::Spine(SpineChoice::Call(cc))) => {
                self.inline_fun(ctx, cc.func, &cc.args, cc.implicit_this, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Builtin {
                op: BuiltinCall::IntAtom,
            })) => {
                // A source-written `Int[e]` does NOT survive resolution as a
                // node of its own — the resolver drops it and re-derives the
                // coercion from context, so `Int[F.v] = 3` resolves to
                // `F.v = 3` and `#(Int[c => plus[3,4] else 0])` to `#(c => …)`
                // (`AstDump` of the resolved tree, mt-127 probes q1/q2/u3).
                // Delegating to `lower_rel` reproduces that: its `Sort::Int`
                // prefix re-inserts the cast exactly where a relation is
                // wanted, which is the same rule the resolver applies. Getting
                // this wrong is observable — keeping the cast here would make
                // `Int[#(Int[3])] = 3` unwrap to `3 = 3` (SAT) where the jar,
                // having deleted the cast, compares `1 = 3` (UNSAT).
                let arg = self.first_box_arg(ctx, e, span)?;
                self.lower_rel(ctx, arg)
            }
            Some(ExprChoice::Spine(SpineChoice::Macro(mc))) => {
                self.replay_macro_rel(ctx, &mc, span)
            }
            Some(ExprChoice::Spine(SpineChoice::Empty(k))) => Ok(self.none_of_arity(k, span)),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "relation-position spine without a recorded resolution".to_owned(),
                span,
            }),
        }
    }

    /// Lowers a relational join spine structurally (translation-ref §2.1): a
    /// `Binary{Join}` is `lower(lhs) . lower(rhs)`; a `BoxJoin` `t[a,b]` folds to
    /// `b . (a . t)`.
    fn lower_join_structural(
        &mut self,
        ctx: Ctx,
        e: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        match self.ast_of(ctx).exprs[e].kind.clone() {
            ExprKind::Binary {
                op: BinOp::Join,
                lhs,
                rhs,
            } => {
                let l = self.lower_rel(ctx, lhs)?;
                let r = self.lower_rel(ctx, rhs)?;
                Ok(self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Join,
                        lhs: l,
                        rhs: r,
                    },
                    span,
                ))
            }
            ExprKind::BoxJoin { target, args } => {
                let mut acc = self.lower_rel(ctx, target)?;
                for a in args {
                    let av = self.lower_rel(ctx, a)?;
                    acc = self.mk_rel(
                        RelExprKind::Binary {
                            op: RelBinOp::Join,
                            lhs: av,
                            rhs: acc,
                        },
                        span,
                    );
                }
                Ok(acc)
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "join spine of unexpected shape".to_owned(),
                span,
            }),
        }
    }

    /// `A <: r` / `r :> A` via product-pad-and-intersect (translation-ref §2.1):
    /// `A <: r` = `(A -> univ^{n-1}) & r`; `r :> A` = `r & (univ^{n-1} -> A)`.
    fn lower_restrict(
        &mut self,
        ctx: Ctx,
        lhs: ExprId,
        rhs: ExprId,
        domain: bool,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        // `A <: r`: set = A (lhs), rel = r (rhs). `r :> A`: rel = r (lhs), set = A (rhs).
        let (set_e, rel_e) = if domain { (lhs, rhs) } else { (rhs, lhs) };
        let rel = self.lower_rel(ctx, rel_e)?;
        let set = self.lower_rel(ctx, set_e)?;
        // The restricted relation's arity, read off the lowered IR (works for any
        // compound, unlike a name-only lookup).
        let arity = self
            .ir_arity(rel)
            .ok_or_else(|| TranslateError::LoweringUnsupported {
                what: "restriction over a relation of unknown arity".to_owned(),
                span,
            })?;
        if arity < 2 {
            // A unary relation's only column *is* its domain/range, so `A <: r`
            // and `r :> A` both reduce to `r & A`.
            return Ok(self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Intersect,
                    lhs: rel,
                    rhs: set,
                },
                span,
            ));
        }
        let univ = self.mk_rel(RelExprKind::Const(RelConst::Univ), span);
        let pad = {
            // univ^{arity-1}
            let mut acc: Option<RelExprId> = None;
            for _ in 0..(arity - 1) {
                acc = Some(match acc {
                    None => univ,
                    Some(a) => self.mk_rel(
                        RelExprKind::Binary {
                            op: RelBinOp::Product,
                            lhs: a,
                            rhs: univ,
                        },
                        span,
                    ),
                });
            }
            acc
        };
        let Some(pad) = pad else {
            return Err(TranslateError::LoweringUnsupported {
                what: "restriction padding".to_owned(),
                span,
            });
        };
        let padded = if domain {
            // set -> univ^{n-1}
            self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Product,
                    lhs: set,
                    rhs: pad,
                },
                span,
            )
        } else {
            // univ^{n-1} -> set
            self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Product,
                    lhs: pad,
                    rhs: set,
                },
                span,
            )
        };
        Ok(self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Intersect,
                lhs: rel,
                rhs: padded,
            },
            span,
        ))
    }

    fn lower_unary_rel(
        &mut self,
        ctx: Ctx,
        op: UnOp,
        expr: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        match op {
            UnOp::Transpose => {
                let r = self.lower_rel(ctx, expr)?;
                Ok(self.mk_rel(
                    RelExprKind::Unary {
                        op: RelUnOp::Transpose,
                        expr: r,
                    },
                    span,
                ))
            }
            UnOp::Closure => {
                let r = self.lower_rel(ctx, expr)?;
                Ok(self.mk_rel(
                    RelExprKind::Unary {
                        op: RelUnOp::Closure,
                        expr: r,
                    },
                    span,
                ))
            }
            UnOp::ReflexiveClosure => {
                let r = self.lower_rel(ctx, expr)?;
                Ok(self.mk_rel(
                    RelExprKind::Unary {
                        op: RelUnOp::ReflexiveClosure,
                        expr: r,
                    },
                    span,
                ))
            }
            // Multiplicity/`seq` decl markers in an expression position: strip.
            UnOp::SetOf | UnOp::ExactlyOf | UnOp::SomeOf | UnOp::LoneOf | UnOp::OneOf => {
                self.lower_rel(ctx, expr)
            }
            // `seq X` in a plain expression position (an `=` side, a join
            // operand): same posture as a multiplicity-marked arrow there —
            // defer typed rather than silently strip the `lone`/contiguity
            // meaning. Field decls and constraint RHS go through
            // `seq_arrow_constraints` instead (mt-046).
            UnOp::SeqOf => Err(TranslateError::LoweringUnsupported {
                what: "`seq` marker in a plain expression position".to_owned(),
                span,
            }),
            UnOp::Prime => {
                let r = self.lower_rel(ctx, expr)?;
                self.mark_temporal("'", span);
                Ok(self.mk_rel(RelExprKind::Prime(r), span))
            }
            _ => Err(TranslateError::LoweringUnsupported {
                what: "unary operator in a relation position".to_owned(),
                span,
            }),
        }
    }

    fn lower_comprehension(
        &mut self,
        ctx: Ctx,
        decls: &[als_syntax::ast::DeclId],
        body: ExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        // A comprehension is a set-builder: its decls are never skolemized
        // (`bind_decls` uses the denied regime), and its body is a non-monotone
        // membership test — block skolemization within it.
        let saved = self.pol;
        self.pol.blocked = true;
        let (comp_decls, disj, pushed) = self.bind_decls(ctx, decls, span)?;
        let body_f = self.lower_formula(ctx, body);
        self.pol = saved;
        for _ in 0..pushed {
            self.binders.pop();
        }
        let mut body_f = body_f?;
        // A `disj` comprehension conjoins pairwise disjointness into the body.
        if let Some(d) = disj {
            body_f = self.mk_formula(FormulaKind::And(vec![d, body_f]), span);
        }
        Ok(self.mk_rel(
            RelExprKind::Comprehension {
                decls: comp_decls,
                body: body_f,
            },
            span,
        ))
    }

    // ============================ integers ============================

    /// Lowers `e` in an integer position — the reference's `cint`
    /// (`TranslateAlloyToKodkod.java:683`), which is `visitThis` followed by
    /// `toInt`. The `toInt` half is [`Self::to_int`]; the `visitThis` half is
    /// [`Self::visit_int`].
    ///
    /// The split is load-bearing, not cosmetic (mt-127). `cint` is reached from
    /// exactly five kinds of position — an arithmetic operand, an int
    /// comparison (`<`/`=<`/`>`/`>=`), the operand of a `Int[·]` cast
    /// (CAST2SIGINT, :888), a `sum` quantifier's body (:1588) and the **else**
    /// branch of an integer if-then-else (:788) — plus wherever the resolver
    /// has inserted an `Int[·]` of its own. Every other position reaches the
    /// expression through `cset`/`toSet`, which never calls `toInt`. So the
    /// same `#(Int[3])` is **3** under `>=` and **1** under `=`, and both are
    /// jar-pinned (`scratchpad/probe/mt127/`, cells a1/a3).
    fn lower_int(&mut self, ctx: Ctx, e: ExprId) -> Result<IntExprId, TranslateError> {
        let raw = self.visit_int(ctx, e)?;
        Ok(self.to_int(raw))
    }

    /// `toInt`'s first arm (`TranslateAlloyToKodkod.java:691-695`): an
    /// `ExprToIntCast` over an `IntToExprCast` is the operand's raw integer,
    /// and the cast operator — cardinality or sum — is **discarded**.
    ///
    /// `Expression.count()` and `Expression.sum()` are Kodkod's two
    /// `ExprToIntCast` constructors, so in mettle's IR that is `Card` or
    /// `AtomToInt` over an [`RelExprKind::IntToAtom`]. The remaining `toInt`
    /// arms are already in place: arm 2 is [`Self::visit_int`]'s `Sort::Rel`
    /// prefix, arms 3 and 4 are the identity and the `AtomToInt` fallback it
    /// ends in.
    ///
    /// Only a **bare** cast unwraps. An `IntToAtom` never wraps an if-then-else
    /// (the reference builds those relationally whenever the then branch
    /// translates to an `Expression` — see [`Self::ite_sort`]), which is why
    /// `#(c => plus[3,4] else 0)` stays a real cardinality (probes t1/u3–u6).
    fn to_int(&self, ie: IntExprId) -> IntExprId {
        let (IntExprKind::Card(rel) | IntExprKind::AtomToInt(rel)) = self.ir.int_exprs[ie].kind
        else {
            return ie;
        };
        match self.ir.rel_exprs[rel].kind {
            RelExprKind::IntToAtom(inner) => inner,
            _ => ie,
        }
    }

    /// The reference's `visitThis` for an integer-position expression: builds
    /// the node with **no** `toInt` peephole, so a caller that needs `cset`
    /// semantics (`=`/`!=`, a union operand, the general set position) sees the
    /// same shape the reference's `toSet` would wrap.
    #[allow(clippy::too_many_lines)] // one arm per integer-position `ExprKind`
    fn visit_int(&mut self, ctx: Ctx, e: ExprId) -> Result<IntExprId, TranslateError> {
        let node = self.ast_of(ctx).exprs[e].clone();
        let span = node.span;
        // An expression that resolves to a *relation* of `Int` atoms in an
        // integer position is implicitly cast (`int[·]`, the reference's
        // CAST2INT) — e.g. `sum a: A | a.n` or `plus[x, a.n]`.
        if self.sort_of(ctx, e) == Sort::Rel {
            let r = self.lower_rel(ctx, e)?;
            // Peephole `int[Int[e]] ≡ e` (translation-ref §2.4): a `fun/…`
            // arithmetic result is `Int`-sorted, so it lowers through `Int[·]`;
            // unwrapping it here keeps the underlying `IntExpr`'s **accumulated
            // overflow** — which `Int[·]` (int→relation) would otherwise drop —
            // so the forbid-mode guard sees it at the comparison (§11.3).
            if let RelExprKind::IntToAtom(ie) = self.ir.rel_exprs[r].kind {
                return Ok(ie);
            }
            return Ok(self.mk_int(IntExprKind::AtomToInt(r), span));
        }
        match node.kind {
            ExprKind::Num(n) => Ok(self.mk_int(IntExprKind::Const(n), span)),
            ExprKind::Unary { op, expr } => match op {
                UnOp::Card => {
                    let r = self.lower_rel(ctx, expr)?;
                    Ok(self.mk_int(IntExprKind::Card(r), span))
                }
                UnOp::IntOf | UnOp::SumOf => {
                    // `int[e]`/`sum e` is CAST2INT → `sum(cset(e))`. The
                    // resolver has already wrapped an int-typed operand in
                    // `Int[·]`, and the reference's `sum()` helper
                    // (`TranslateAlloyToKodkod.java:905-909`) strips that cast
                    // straight back off — so the operand is read through `cint`,
                    // peephole and all (probe s9, `int[#(Int[3])] = 3` is SAT).
                    if self.sort_of(ctx, expr) == Sort::Int {
                        return self.lower_int(ctx, expr);
                    }
                    let r = self.lower_rel(ctx, expr)?;
                    Ok(self.mk_int(IntExprKind::AtomToInt(r), span))
                }
                _ => Err(TranslateError::LoweringUnsupported {
                    what: "unary operator in an integer position".to_owned(),
                    span,
                }),
            },
            ExprKind::Binary { op, lhs, rhs } => {
                if self.minus_folds_to_min(ctx, op, lhs, rhs) {
                    // `toInt` of the folded constant, unwrapped — no `.sum()`
                    // round-trip. See [`Self::minus_folds_to_min`].
                    return Ok(self.mk_int(IntExprKind::Const(int_min(self.bitwidth)), span));
                }
                if let Some(iop) = int_binop(op) {
                    let l = self.lower_int(ctx, lhs)?;
                    let r = self.lower_int(ctx, rhs)?;
                    Ok(self.mk_int(
                        IntExprKind::Binary {
                            op: iop,
                            lhs: l,
                            rhs: r,
                        },
                        span,
                    ))
                } else {
                    Err(TranslateError::LoweringUnsupported {
                        what: "binary operator in an integer position".to_owned(),
                        span,
                    })
                }
            }
            ExprKind::BoxJoin { .. } => {
                // `int[e]`/`sum[e]` → AtomToInt of the operand.
                match self.choice(ctx, e).cloned() {
                    Some(ExprChoice::Spine(SpineChoice::Builtin {
                        op: BuiltinCall::IntCast,
                    })) => {
                        // Same `sum()`-helper collapse as the `UnOp::IntOf` arm.
                        let arg = self.first_box_arg(ctx, e, span)?;
                        if self.sort_of(ctx, arg) == Sort::Int {
                            return self.lower_int(ctx, arg);
                        }
                        let r = self.lower_rel(ctx, arg)?;
                        Ok(self.mk_int(IntExprKind::AtomToInt(r), span))
                    }
                    Some(ExprChoice::Spine(SpineChoice::Call(cc))) => {
                        self.inline_fun_int(ctx, cc.func, &cc.args, cc.implicit_this, span)
                    }
                    Some(ExprChoice::Spine(SpineChoice::Macro(mc))) => {
                        self.replay_macro_int(ctx, &mc, span)
                    }
                    _ => Err(TranslateError::LoweringUnsupported {
                        what: "integer-position spine".to_owned(),
                        span,
                    }),
                }
            }
            ExprKind::Quant {
                quant: Quant::Sum,
                decls,
                body,
            } => self.lower_sum(ctx, &decls, body, span),
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let saved = self.pol;
                self.pol.blocked = true;
                let c = self.lower_formula(ctx, cond);
                self.pol = saved;
                let c = c?;
                // `visit(ExprITE)` is asymmetric (`:776-789`): the then branch
                // is `visitThis(x.left)` — whose Kodkod class is what picks the
                // arm in the first place, so it is never coerced — while the
                // else branch is `cint(x.right)`. Probes y7 (`(some Node =>
                // #(Int[3]) else 0) >= 3` is UNSAT: the then branch stays a
                // cardinality) and s1 (`(no Node => #(Int[1]) else
                // #(plus[3,4])) >= 7` is SAT: the else branch unwraps).
                let t = self.visit_int(ctx, then_branch)?;
                let el = self.lower_int(ctx, else_branch)?;
                Ok(self.mk_int(
                    IntExprKind::IfThenElse {
                        cond: c,
                        then_branch: t,
                        else_branch: el,
                    },
                    span,
                ))
            }
            ExprKind::Name(_) | ExprKind::AtName(_) => {
                // A 0-ary fun returning an int, inlined; or an `Int`-sorted
                // module-level macro, replayed.
                match self.choice(ctx, e).cloned() {
                    Some(ExprChoice::Name(NameChoice::Call0(func))) => {
                        self.inline_fun_int(ctx, func, &[], true, span)
                    }
                    Some(ExprChoice::Name(NameChoice::Macro(mc))) => {
                        self.replay_macro_int(ctx, &mc, span)
                    }
                    _ => Err(TranslateError::LoweringUnsupported {
                        what: "integer-position name".to_owned(),
                        span,
                    }),
                }
            }
            // `visit(ExprLet)` (`:795-802`) is a pass-through: it stores
            // `visitThis(x.expr)` and returns `visitThis(x.sub)`, both raw, so
            // the `toInt` peephole fires at the enclosing `cint` and not here
            // (probes b3/b4, t7).
            ExprKind::Let { bindings, body } => {
                let pushed = self.push_let_bindings(ctx, &bindings)?;
                let r = self.visit_int(ctx, body);
                for _ in 0..pushed {
                    self.binders.pop();
                }
                r
            }
            // A single-element block `{ e }` (a fun body) is just `e`.
            ExprKind::Block(exprs) if exprs.len() == 1 => self.visit_int(ctx, exprs[0]),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "unexpected integer-position expression".to_owned(),
                span,
            }),
        }
    }

    fn lower_sum(
        &mut self,
        ctx: Ctx,
        decls: &[als_syntax::ast::DeclId],
        body: ExprId,
        span: Span,
    ) -> Result<IntExprId, TranslateError> {
        // `sum` desugars to nested single-var `Sum` (IR shape).
        let mut var_bounds: Vec<(crate::ir::VarId, RelExprId)> = Vec::new();
        let mut pushed = 0;
        for &d in decls {
            let decl = self.ast_of(ctx).decls[d].clone();
            if decl.is_bound_disj {
                return Err(bound_disj_unpinned(self.ast_of(ctx).exprs[decl.bound].span));
            }
            let bound = self.lower_decl_bound_set(ctx, &decl)?;
            for name in &decl.names {
                let vid = self.ir.vars.alloc(Var {
                    name: name.text.clone(),
                    arity: 1,
                    span: name.span,
                });
                var_bounds.push((vid, bound));
                self.binders.push((name.text.clone(), Binding::Var(vid)));
                pushed += 1;
            }
        }
        let saved = self.pol;
        self.pol.blocked = true;
        let body_i = self.lower_int(ctx, body);
        self.pol = saved;
        for _ in 0..pushed {
            self.binders.pop();
        }
        let mut acc = body_i?;
        for (vid, bound) in var_bounds.into_iter().rev() {
            acc = self.mk_int(
                IntExprKind::Sum {
                    var: vid,
                    bound,
                    body: acc,
                },
                span,
            );
        }
        Ok(acc)
    }

    // ============================ quantifiers ============================

    /// Lowers a quantifier (translation-ref §2.3): `all`/`some` desugar to nested
    /// single-var `Quant`; `no x | φ` ⇒ `all x | ¬φ`; `one`/`lone x | φ` via the
    /// comprehension-cardinality route (`one {x | φ}` / `lone {x | φ}`).
    fn lower_quant(
        &mut self,
        ctx: Ctx,
        quant: Quant,
        decls: &[als_syntax::ast::DeclId],
        body: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        match quant {
            Quant::Sum => Err(TranslateError::LoweringUnsupported {
                what: "`sum` in a formula position".to_owned(),
                span,
            }),
            Quant::All | Quant::Some | Quant::No => {
                // Skolemization regime (translation-ref §10.6): a higher-order
                // decl skolemizes iff this quantifier is an effective existential
                // in the goal's NNF and nothing above it is blocked. `some` is
                // effective-existential at positive polarity; `all`/`no` (`= all
                // ¬`) at negative polarity.
                let positive = self.pol.positive;
                let effective_existential = match quant {
                    Quant::Some => positive,
                    Quant::All | Quant::No => !positive,
                    Quant::One | Quant::Lone | Quant::Sum => unreachable!("handled elsewhere"),
                };
                let regime = if effective_existential && !self.pol.blocked {
                    SkolemRegime::Allowed
                } else {
                    SkolemRegime::Denied
                };
                let bound_decls = self.bind_decls_vars(ctx, decls, span, regime)?;
                let pushed = bound_decls.pushed;

                // Body polarity: `all` keeps it (monotone), `no` flips it
                // (`all ¬`); the body is under a universal iff this quant is
                // effective-universal.
                let body_positive = if matches!(quant, Quant::No) {
                    !positive
                } else {
                    positive
                };
                let saved = self.pol;
                self.pol = Pol {
                    positive: body_positive,
                    blocked: self.pol.blocked || !effective_existential,
                };
                let body_f = self.lower_formula(ctx, body);
                self.pol = saved;
                for _ in 0..pushed {
                    self.binders.pop();
                }
                let mut inner = body_f?;
                // `no` = `all ¬`.
                let kind = if matches!(quant, Quant::Some) {
                    QuantKind::Some
                } else {
                    QuantKind::All
                };
                if matches!(quant, Quant::No) {
                    inner = self.not(inner, span);
                }
                // Guards: FO-decl pairwise disjointness + every skolem decl's
                // membership/multiplicity/disjointness constraint. `some`
                // conjoins them (`∃`, discharged in place); `all`/`no` make them
                // the antecedent (`∀`-shape, the enclosing `!` of a `check`
                // discharges the effective `∃` — probe T9c).
                let mut guards: Vec<FormulaId> = Vec::new();
                if let Some(d) = bound_decls.fo_disj {
                    guards.push(d);
                }
                guards.extend(bound_decls.skolem_constraints);
                if !guards.is_empty() {
                    inner = if matches!(quant, Quant::Some) {
                        guards.push(inner);
                        self.mk_formula(FormulaKind::And(guards), span)
                    } else {
                        let antecedent = self.conjoin(guards, span);
                        self.mk_formula(
                            FormulaKind::Implies {
                                antecedent,
                                consequent: inner,
                            },
                            span,
                        )
                    };
                }
                let mut acc = inner;
                for (vid, bound) in bound_decls.fo.into_iter().rev() {
                    acc = self.mk_formula(
                        FormulaKind::Quant {
                            kind,
                            var: vid,
                            bound,
                            body: acc,
                        },
                        span,
                    );
                }
                Ok(acc)
            }
            Quant::One | Quant::Lone => {
                // `one/lone x: B | φ` ⇒ `one/lone {x: B | φ}`.
                let comp = self.lower_comprehension(ctx, decls, body, span)?;
                let test = if matches!(quant, Quant::One) {
                    MultTest::One
                } else {
                    MultTest::Lone
                };
                Ok(self.mk_formula(FormulaKind::MultTest { test, expr: comp }, span))
            }
        }
    }

    /// Binds a decl list, splitting **first-order** decls (bound as fresh IR
    /// quantifier vars over the bound's tuples) from **higher-order** decls
    /// (translation-ref §2.3/§10.6). A HO decl ranges over *sub-relations*, not
    /// tuples — a non-`one` unary marker (`some r: set A`) or a multiplicity-marked
    /// arrow (`some r: A one -> one B`). Under [`SkolemRegime::Allowed`] a HO decl
    /// is **skolemized** (a fresh free relation + its membership/multiplicity
    /// constraint, [`Self::skolem_decl`]); under [`SkolemRegime::Denied`] it is a
    /// typed `HigherOrder` defer — never a per-tuple wrong verdict (a plain product
    /// `A -> B` stays first-order: one pair per binding, the jar's reading).
    fn bind_decls_vars(
        &mut self,
        ctx: Ctx,
        decls: &[als_syntax::ast::DeclId],
        span: Span,
        regime: SkolemRegime,
    ) -> Result<BoundDecls, TranslateError> {
        let mut out = BoundDecls::default();
        let mut disj_parts: Vec<FormulaId> = Vec::new();
        for &d in decls {
            let decl = self.ast_of(ctx).decls[d].clone();
            if decl.is_bound_disj {
                return Err(bound_disj_unpinned(self.ast_of(ctx).exprs[decl.bound].span));
            }
            if self.decl_is_higher_order(ctx, decl.bound) {
                let bound_span = self.ast_of(ctx).exprs[decl.bound].span;
                if !matches!(regime, SkolemRegime::Allowed) {
                    return Err(TranslateError::HigherOrder { span: bound_span });
                }
                self.has_higher_order_skolem = true;
                // Skolemize each name of the group; collect them for a `disj`.
                let mut group: Vec<RelExprId> = Vec::new();
                for name in &decl.names {
                    let x = self.mint_skolem(ctx, &name.text, &decl, name.span)?;
                    out.skolem_constraints
                        .extend(self.skolem_decl_constraints(ctx, x, &decl, bound_span)?);
                    self.binders.push((name.text.clone(), Binding::Expr(x)));
                    out.pushed += 1;
                    group.push(x);
                }
                if decl.is_disj && group.len() >= 2 {
                    self.push_pairwise_disjoint(&group, span, &mut out.skolem_constraints);
                }
                continue;
            }
            let bound = self.lower_decl_bound_set(ctx, &decl)?;
            // A first-order quantified var ranges over the bound's *tuples* (the
            // decl's implicit `one`, translation-ref §2.3) — its arity is the
            // bound's. `all R: univ->univ` binds `R` to one pair at a time,
            // exactly the jar's first-order reading (closure.als[0] is jar-SAT).
            let arity =
                self.ir_arity(bound)
                    .ok_or_else(|| TranslateError::LoweringUnsupported {
                        what: "quantifier over a bound of unknown arity".to_owned(),
                        span,
                    })?;
            // First-order skolemization (mt-047, translation-ref §15): a top-level
            // effective-existential FO decl (regime `Allowed`) becomes a skolem
            // constant relation — one per name, membership + `one`, plus `disj`
            // conjuncts — dropping the quantifier so SB-0 enumeration counts each
            // witness (K4). Every name in the group shares `bound`, so a single
            // abstract-upper probe decides the whole group; a bound with no sound
            // upper falls through to ordinary quantifier vars (correct verdict,
            // pre-mt-047 count).
            if let (SkolemRegime::Allowed, Some(upper)) = (regime, self.abstract_upper(bound)) {
                let mut group: Vec<RelExprId> = Vec::new();
                for name in &decl.names {
                    let x = self.fo_skolemize(
                        &name.text,
                        bound,
                        arity,
                        upper.clone(),
                        name.span,
                        &mut out.skolem_constraints,
                    );
                    self.binders.push((name.text.clone(), Binding::Expr(x)));
                    out.pushed += 1;
                    group.push(x);
                }
                if decl.is_disj && group.len() >= 2 {
                    self.push_pairwise_disjoint(&group, span, &mut out.skolem_constraints);
                }
                continue;
            }
            let mut group: Vec<RelExprId> = Vec::new();
            for name in &decl.names {
                let vid = self.ir.vars.alloc(Var {
                    name: name.text.clone(),
                    arity,
                    span: name.span,
                });
                out.fo.push((vid, bound));
                self.var_bound.insert(vid, bound);
                self.binders.push((name.text.clone(), Binding::Var(vid)));
                out.pushed += 1;
                group.push(self.mk_rel(RelExprKind::Var(vid), name.span));
            }
            if decl.is_disj && group.len() >= 2 {
                self.push_pairwise_disjoint(&group, span, &mut disj_parts);
            }
        }
        out.fo_disj = if disj_parts.is_empty() {
            None
        } else {
            Some(self.conjoin(disj_parts, span))
        };
        Ok(out)
    }

    /// Whether a decl bound is genuinely higher-order (translation-ref §10.6): a
    /// non-`one` unary multiplicity marker, or a multiplicity-marked arrow. A
    /// plain product `A -> B` (no marks) is first-order (one pair per binding).
    fn decl_is_higher_order(&self, ctx: Ctx, bound: ExprId) -> bool {
        if let ExprKind::Unary { op, .. } = &self.ast_of(ctx).exprs[bound].kind {
            if is_mult_marker(*op) && !matches!(op, UnOp::OneOf) {
                return true;
            }
        }
        self.bound_is_higher_order(ctx, bound)
    }

    /// Mints a fresh skolem relation `$<cmdLabel>_<var>` for a higher-order decl
    /// (translation-ref §10.6, probe T9): arity = the decl's bound-set arity, lower
    /// `{}`, upper = the sound abstract upper of the bound's denotation. Records
    /// `(rel, bound)` for [`LoweredGoal::skolem_bounds`] and returns the relation
    /// expression the var binds to.
    fn mint_skolem(
        &mut self,
        ctx: Ctx,
        var: &str,
        decl: &Decl,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let set_expr = self.lower_decl_bound_set(ctx, decl)?;
        let arity = self
            .ir_arity(set_expr)
            .ok_or(TranslateError::HigherOrder { span })?;
        let upper = self
            .abstract_upper(set_expr)
            .ok_or(TranslateError::HigherOrder { span })?;
        debug_assert_eq!(upper.arity(), arity, "skolem abstract-upper arity mismatch");
        Ok(self.alloc_skolem(var, arity, upper, span))
    }

    /// Allocates a fresh skolem relation `$<cmdLabel>_<var>` (empty label ⇒
    /// `$<var>`, translation-ref §15) of the given arity, bounded `[{}, upper]`,
    /// records it in [`Self::skolem_bounds`], and returns the relation expression
    /// the var binds to. The shared allocation core for both the higher-order
    /// skolem path ([`Self::mint_skolem`], mt-038) and the first-order one
    /// ([`Self::fo_skolemize`], mt-047).
    fn alloc_skolem(&mut self, var: &str, arity: usize, upper: TupleSet, span: Span) -> RelExprId {
        // §15 naming: inside an inlined func/pred body the prefix is the
        // *innermost function's* tail label, not the command's (`run foo { q }`
        // with `some x` in `q` → `$q_x`); a `$` in the label drops the prefix,
        // same as for command labels.
        let label = match self.inline_stack.last() {
            Some(&f) => {
                let n = &self.world.funcs[f].name;
                if n.contains('$') {
                    ""
                } else {
                    n.as_str()
                }
            }
            None => self.cmd_label.as_str(),
        };
        let base = if label.is_empty() {
            format!("${var}")
        } else {
            format!("${label}_{var}")
        };
        // Uniquify against every skolem name already minted this command (the
        // jar's `un.make`, translation-ref §15) — display-only; distinct `RelId`s
        // already keep the relations apart for the verdict/count.
        let mut name = base.clone();
        let mut k = 2u32;
        while !self.skolem_names.insert(name.clone()) {
            name = format!("{base}_{k}");
            k += 1;
        }
        // A skolem constant is static: skolemization is switched off entirely
        // under any temporal operator (`Skolemizer.java:494-526`,
        // alloy6-temporal.md §(d)), so a minted skolem always witnesses a
        // state-independent, top-level existential.
        let rel = self.ir.relations.alloc(Relation {
            name,
            arity,
            span,
            mutability: Mutability::Static,
        });
        let lower = TupleSet::empty(arity);
        self.skolem_bounds.push((rel, RelBound::new(lower, upper)));
        self.mk_rel(RelExprKind::Relation(rel), span)
    }

    /// First-order skolemization (mt-047, translation-ref §15): mints a skolem
    /// **constant** relation for a top-level effective-existential first-order
    /// decl `var: bound` (a plain sig quantifier, a `one`-marked decl, or a plain
    /// unmarked product) whose lowered bound is `bound` with sound abstract
    /// `upper`. Pushes the decl's constraints onto `out` — membership `$var in
    /// bound` plus `one $var` (a first-order quant var ranges over a single tuple
    /// of its bound, the jar's scalar reading) — and returns the skolem's relation
    /// expression. The caller decides eligibility: it skolemizes only when
    /// [`Self::abstract_upper`] gave an upper (a comprehension / `Int[·]` / ITE /
    /// prime bound has none, and there the caller keeps an ordinary first-order
    /// quantifier — correct verdict, pre-mt-047 count).
    fn fo_skolemize(
        &mut self,
        var: &str,
        bound: RelExprId,
        arity: usize,
        upper: TupleSet,
        span: Span,
        out: &mut Vec<FormulaId>,
    ) -> RelExprId {
        debug_assert_eq!(
            upper.arity(),
            arity,
            "fo-skolem abstract-upper arity mismatch"
        );
        let x = self.alloc_skolem(var, arity, upper, span);
        out.push(self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: x,
                rhs: bound,
            },
            span,
        ));
        out.push(self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::One,
                expr: x,
            },
            span,
        ));
        x
    }

    /// The membership + multiplicity constraint conjuncts on a skolem relation
    /// `x`, from its decl's bound shape (translation-ref §10.6, probes T9a/b/f/g):
    /// a unary marker → `x in A` (+ `some`/`lone` test); a mult-marked (or plain
    /// higher-arity) arrow → the shared [`Self::arrow_value_constraint`]; any other
    /// bound → membership only.
    fn skolem_decl_constraints(
        &mut self,
        ctx: Ctx,
        x: RelExprId,
        decl: &Decl,
        span: Span,
    ) -> Result<Vec<FormulaId>, TranslateError> {
        let bound = decl.bound;
        match self.ast_of(ctx).exprs[bound].kind.clone() {
            ExprKind::Unary { op, expr } if is_mult_marker(op) => {
                // `exactly A` means `x = A`, not `x in A`; defer rather than
                // emit a weaker membership (never a wrong verdict, STYLE E5).
                if matches!(op, UnOp::ExactlyOf) {
                    return Err(TranslateError::HigherOrder { span });
                }
                let rel = self.lower_rel(ctx, expr)?;
                let mut cs = vec![self.mk_formula(
                    FormulaKind::RelCompare {
                        op: RelCmpOp::Subset,
                        lhs: x,
                        rhs: rel,
                    },
                    span,
                )];
                if let Some(test) = mult_of_marker(op) {
                    cs.push(self.mk_formula(FormulaKind::MultTest { test, expr: x }, span));
                }
                Ok(cs)
            }
            ExprKind::Arrow {
                lhs,
                lhs_mult,
                rhs_mult,
                rhs,
            } => self.arrow_value_constraint(ctx, x, lhs, lhs_mult, rhs_mult, rhs, span, &mut 0),
            _ => {
                // A plain (non-arrow, non-marked) bound of arity ≥ 2, e.g. a
                // run-pred param `r: someBinaryRel`: membership only (default
                // `set`).
                let rel = self.lower_rel(ctx, bound)?;
                Ok(vec![self.mk_formula(
                    FormulaKind::RelCompare {
                        op: RelCmpOp::Subset,
                        lhs: x,
                        rhs: rel,
                    },
                    span,
                )])
            }
        }
    }

    /// A sound **upper bound** for the denotation of a lowered relation
    /// expression, by abstract evaluation against the existing [`Bounds`]
    /// (translation-ref §10.6): sig/field relations → their upper set, constants,
    /// product/union/intersect/difference/override/join/transpose/closure. Returns
    /// `None` for anything not soundly boundable (a bound depending on an outer
    /// variable, a comprehension, an `Int[·]` cast, an ITE, a prime) → the caller
    /// defers. Deterministic: every set is `BTreeSet`-backed.
    fn abstract_upper(&self, r: RelExprId) -> Option<TupleSet> {
        match &self.ir.rel_exprs[r].kind {
            // A relation's upper comes from the bounds builder — or, for a
            // skolem minted earlier in THIS lowering, from `skolem_bounds` (the
            // builder never saw it). Without the skolem arm, a decl bounded by
            // an earlier skolem (`some b: Book, n: b.names | …` after `b`
            // skolemizes) silently loses its upper: an FO decl then falls back
            // to a quantifier (jar-divergent SB-0 count — addressBook2e[3]) and
            // a HO decl falls back to a typed HigherOrder defer.
            RelExprKind::Relation(rel) => match self.bounds.bounds.get(*rel) {
                Some(b) => Some(b.upper().clone()),
                None => self
                    .skolem_bounds
                    .iter()
                    .find(|(sr, _)| sr == rel)
                    .map(|(_, b)| b.upper().clone()),
            },
            RelExprKind::Const(RelConst::None) => Some(TupleSet::empty(1)),
            RelExprKind::Const(RelConst::Univ) => Some(self.univ_upper()),
            RelExprKind::Const(RelConst::Iden) => Some(self.iden_upper()),
            RelExprKind::Binary { op, lhs, rhs } => {
                let a = self.abstract_upper(*lhs)?;
                // `a - b ⊆ a` and `a & b ⊆ a` need no upper for `b` — so a
                // right operand mettle cannot bound (a comprehension) does not
                // sink the whole bound (this is what unlocks messaging.als's
                // `some r: (MsgsLiveOnTick[t] - {…}) one -> one …`).
                match op {
                    RelBinOp::Diff => Some(a),
                    RelBinOp::Intersect => match self.abstract_upper(*rhs) {
                        Some(b) => tupleset_intersect(&a, &b),
                        None => Some(a),
                    },
                    RelBinOp::Product => Some(tupleset_product(&a, &self.abstract_upper(*rhs)?)),
                    RelBinOp::Union => tupleset_union(&a, &self.abstract_upper(*rhs)?),
                    // `a ++ b ⊆ a ∪ b`: sound only with `b`'s upper.
                    RelBinOp::Override => tupleset_union(&a, &self.abstract_upper(*rhs)?),
                    RelBinOp::Join => tupleset_join(&a, &self.abstract_upper(*rhs)?),
                }
            }
            RelExprKind::Unary { op, expr } => {
                let a = self.abstract_upper(*expr)?;
                match op {
                    RelUnOp::Transpose => tupleset_transpose(&a),
                    RelUnOp::Closure => tupleset_closure(&a),
                    RelUnOp::ReflexiveClosure => {
                        let c = tupleset_closure(&a)?;
                        tupleset_union(&c, &self.iden_upper())
                    }
                }
            }
            // A bound variable is over-approximated by the upper of its own
            // declared bound (an enclosing existential — see `var_bound`): a
            // sound, `t`-independent upper for a skolem bound like `f[t]`.
            RelExprKind::Var(v) => {
                let bound = *self.var_bound.get(v)?;
                self.abstract_upper(bound)
            }
            // A comprehension, an int-atom cast, a prime, or an ITE is not a
            // constant over the bounds — no sound static upper (defer).
            RelExprKind::Prime(_)
            | RelExprKind::IfThenElse { .. }
            | RelExprKind::Comprehension { .. }
            | RelExprKind::IntToAtom(_) => None,
        }
    }

    /// `univ`'s upper bound: every atom, unary.
    fn univ_upper(&self) -> TupleSet {
        let mut ts = TupleSet::empty(1);
        for (atom, _) in self.bounds.bounds.universe.iter() {
            ts.insert(Tuple::new(vec![atom]));
        }
        ts
    }

    /// `iden`'s upper bound: `{(a, a) | a ∈ univ}`.
    fn iden_upper(&self) -> TupleSet {
        let mut ts = TupleSet::empty(2);
        for (atom, _) in self.bounds.bounds.universe.iter() {
            ts.insert(Tuple::new(vec![atom, atom]));
        }
        ts
    }

    /// Like [`Self::bind_decls_vars`] but returns [`CompDecl`]s for a
    /// comprehension (each var + its unary bound). Comprehension decls are never
    /// skolemized (a set-builder is genuinely higher-order over its members), so it
    /// always uses [`SkolemRegime::Denied`] — a HO comprehension decl defers.
    fn bind_decls(
        &mut self,
        ctx: Ctx,
        decls: &[als_syntax::ast::DeclId],
        span: Span,
    ) -> Result<(Vec<CompDecl>, Option<FormulaId>, usize), TranslateError> {
        let bound = self.bind_decls_vars(ctx, decls, span, SkolemRegime::Denied)?;
        debug_assert!(
            bound.skolem_constraints.is_empty(),
            "denied regime cannot mint skolems"
        );
        let comp = bound
            .fo
            .into_iter()
            .map(|(var, bound)| CompDecl { var, bound })
            .collect();
        Ok((comp, bound.fo_disj, bound.pushed))
    }

    fn push_pairwise_disjoint(
        &mut self,
        group: &[RelExprId],
        span: Span,
        out: &mut Vec<FormulaId>,
    ) {
        for i in 0..group.len() {
            for j in (i + 1)..group.len() {
                let inter = self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Intersect,
                        lhs: group[i],
                        rhs: group[j],
                    },
                    span,
                );
                out.push(self.mk_formula(
                    FormulaKind::MultTest {
                        test: MultTest::No,
                        expr: inter,
                    },
                    span,
                ));
            }
        }
    }

    /// Whether a quantifier decl bound is genuinely **higher-order** — it ranges
    /// over sub-relations, not tuples — so it cannot be lowered first-order and
    /// must defer (translation-ref §2.3). A plain product `A -> B` (no marks) is
    /// first-order (one pair per binding, closure.als[0]); an arrow carrying any
    /// multiplicity mark (`A one -> one B`, `Node lone -> Node`) constrains the
    /// whole relation the var ranges over, which is second-order. Walks the arrow
    /// tree so a mark on any column is caught.
    fn bound_is_higher_order(&self, ctx: Ctx, e: ExprId) -> bool {
        match &self.ast_of(ctx).exprs[e].kind {
            ExprKind::Arrow {
                lhs,
                lhs_mult,
                rhs_mult,
                rhs,
            } => {
                lhs_mult.is_some()
                    || rhs_mult.is_some()
                    || self.bound_is_higher_order(ctx, *lhs)
                    || self.bound_is_higher_order(ctx, *rhs)
            }
            _ => false,
        }
    }

    /// Lowers a declaration bound to its **set** relation, stripping any
    /// multiplicity/`seq` marker (the marker constrains the bound, handled at the
    /// quantifier/field level, not the bound value).
    fn lower_decl_bound_set(&mut self, ctx: Ctx, decl: &Decl) -> Result<RelExprId, TranslateError> {
        self.lower_bound_expr_set(ctx, decl.bound)
    }

    /// A decl bound's *set* value: the multiplicity marker (`one`/`some`/`set`/…)
    /// is the binder's business, so it is stripped here and the inner expression
    /// lowered on its own.
    fn lower_bound_expr_set(
        &mut self,
        ctx: Ctx,
        bound: ExprId,
    ) -> Result<RelExprId, TranslateError> {
        let ast = self.ast_of(ctx);
        let inner = match &ast.exprs[bound].kind {
            ExprKind::Unary { op, expr } if is_mult_marker(*op) => *expr,
            _ => bound,
        };
        self.lower_rel_stripped(ctx, inner)
    }

    /// Lowers an arrow tree to its plain-product value, deliberately ignoring
    /// multiplicity marks. Only for callers that enforce the marks themselves —
    /// [`Self::arrow_value_constraint`]'s membership product and the skolem
    /// bound of [`Self::lower_decl_bound_set`]; everywhere else, a marked arrow
    /// must go through `lower_rel` and hit its typed defer instead of being
    /// silently weakened.
    fn lower_rel_stripped(&mut self, ctx: Ctx, e: ExprId) -> Result<RelExprId, TranslateError> {
        if let ExprKind::Arrow { lhs, rhs, .. } = self.ast_of(ctx).exprs[e].kind {
            let span = self.span_of(ctx, e);
            let l = self.lower_rel_stripped(ctx, lhs)?;
            let r = self.lower_rel_stripped(ctx, rhs)?;
            return Ok(self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Product,
                    lhs: l,
                    rhs: r,
                },
                span,
            ));
        }
        self.lower_rel(ctx, e)
    }

    // ============================ calls / macros ============================

    /// Inlines a pred body as a formula, binding each parameter to the
    /// (lowered) argument (translation-ref §3.5). `implicit_this` mirrors the
    /// call's [`als_types::choice::CallChoice::implicit_this`]: when `true` the
    /// receiver is the caller's current `this` (a bare call inside another
    /// receiver-pred/appended-fact body); when `false` the receiver is an
    /// **explicit** join-syntax argument (`ks.iterator[..]` desugars to
    /// `iterator[ks, ..]`, resolution §3.5) already present as `args[0]`.
    fn inline_pred(
        &mut self,
        ctx: Ctx,
        func: FuncIdx,
        args: &[ExprId],
        implicit_this: bool,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        let (fmod, body, pushed) = self.bind_call_params(ctx, func, args, implicit_this, span)?;
        let fctx = self.ctx(fmod);
        let r = self.lower_formula(fctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        self.inline_stack.pop();
        r
    }

    /// Inlines a fun body as a relation. See [`Self::inline_pred`] for
    /// `implicit_this`.
    fn inline_fun(
        &mut self,
        ctx: Ctx,
        func: FuncIdx,
        args: &[ExprId],
        implicit_this: bool,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let (fmod, body, pushed) = self.bind_call_params(ctx, func, args, implicit_this, span)?;
        let fctx = self.ctx(fmod);
        let r = self.lower_rel(fctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        self.inline_stack.pop();
        r
    }

    /// Inlines a fun body as an integer. See [`Self::inline_pred`] for
    /// `implicit_this`.
    fn inline_fun_int(
        &mut self,
        ctx: Ctx,
        func: FuncIdx,
        args: &[ExprId],
        implicit_this: bool,
        span: Span,
    ) -> Result<IntExprId, TranslateError> {
        // `visit(ExprCall)` (`:1010-1050`) returns `visitThis(body)` unchanged,
        // so the callee's body is raw at the call site and the `toInt` peephole
        // fires only at the enclosing `cint` (probes b1/b2).
        let (fmod, body, pushed) = self.bind_call_params(ctx, func, args, implicit_this, span)?;
        let fctx = self.ctx(fmod);
        let r = self.visit_int(fctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        self.inline_stack.pop();
        r
    }

    /// Binds a call's parameters to its (lowered) argument expressions and
    /// returns the func's module, body, and how many binders were pushed. Guards
    /// self-recursion (the reference rejects recursive funcs/preds) with a bound.
    fn bind_call_params(
        &mut self,
        ctx: Ctx,
        func: FuncIdx,
        args: &[ExprId],
        implicit_this: bool,
        span: Span,
    ) -> Result<(ModuleId, ExprId, usize), TranslateError> {
        // Recursion guard: refuse if this func is already being inlined.
        if self.inline_stack.contains(&func) {
            return Err(TranslateError::LoweringUnsupported {
                what: "recursive func/pred call".to_owned(),
                span,
            });
        }
        let f = self.world.funcs[func].clone();
        let params = f.params.clone();
        let has_recv = params.first().is_some_and(|p| p.name == "this");
        // Lower each explicit argument in the *caller's* context first. When the
        // receiver is explicit (`implicit_this` false), it is already `args[0]`
        // (`CallChoice::args` is "in parameter order", receiver included
        // whenever it isn't implicit) — lowered here like any other argument.
        let mut arg_rels: Vec<RelExprId> = Vec::with_capacity(args.len());
        for &a in args {
            arg_rels.push(self.lower_rel(ctx, a)?);
        }
        let mut pushed = 0usize;
        let mut arg_iter = arg_rels.into_iter();
        for p in &params {
            if p.name == "this" && has_recv {
                let this = if implicit_this {
                    // Bind the receiver `this` to the caller's current `this`.
                    self.lookup_binder("this", span)?
                } else {
                    // The receiver is the join's explicit LHS, first in `args`.
                    arg_iter
                        .next()
                        .ok_or_else(|| TranslateError::LoweringUnsupported {
                            what: format!("call to `{}`: missing receiver", f.name),
                            span,
                        })?
                };
                self.binders.push(("this".to_owned(), Binding::Expr(this)));
                pushed += 1;
                continue;
            }
            let Some(av) = arg_iter.next() else {
                return Err(TranslateError::LoweringUnsupported {
                    what: format!("call to `{}`: too few arguments", f.name),
                    span,
                });
            };
            self.binders.push((p.name.clone(), Binding::Expr(av)));
            pushed += 1;
        }
        self.inline_stack.push(func);
        Ok((f.module, f.body, pushed))
    }

    /// Replays a macro expansion as a formula (translation-ref §3.7): bind each
    /// parameter to its (lowered) argument, then lower the body in the macro's
    /// module + nested choice table.
    fn replay_macro_formula(
        &mut self,
        caller: Ctx,
        mc: &als_types::MacroChoice,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        let pushed = self.bind_macro(caller, mc, span)?;
        let ctx = Ctx {
            module: mc.body_module,
            choices: &mc.body_choices,
            ast: None,
        };
        let body = self.world.macros[mc.macro_id].body;
        let r = self.lower_formula(ctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        r
    }

    fn replay_macro_rel(
        &mut self,
        caller: Ctx,
        mc: &als_types::MacroChoice,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let pushed = self.bind_macro(caller, mc, span)?;
        let ctx = Ctx {
            module: mc.body_module,
            choices: &mc.body_choices,
            ast: None,
        };
        let body = self.world.macros[mc.macro_id].body;
        let r = self.lower_rel(ctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        r
    }

    /// The integer-position twin of [`Self::replay_macro_rel`]. A macro whose
    /// body is `Int`-sorted (`#A`, a bare numeral, the `0-(max+1)` fold) never
    /// reaches `lower_rel`'s macro arm: the caller's `Sort::Int` classification
    /// routes it straight here. The reference inlines the macro *before*
    /// translating, so the body's own translated class is what the surrounding
    /// arithmetic sees — replaying the body through `visit_int` reproduces that
    /// exactly, including the §2.4 peephole, the `0-(max+1)` fold and the
    /// forbid-mode overflow flag, with no arm of its own (translation-ref
    /// §10.7j). Raw, like the fun-call and `let` pass-throughs: the `toInt`
    /// peephole belongs to the enclosing `cint`, not to the inlining.
    fn replay_macro_int(
        &mut self,
        caller: Ctx,
        mc: &als_types::MacroChoice,
        span: Span,
    ) -> Result<IntExprId, TranslateError> {
        let pushed = self.bind_macro(caller, mc, span)?;
        let ctx = Ctx {
            module: mc.body_module,
            choices: &mc.body_choices,
            ast: None,
        };
        let body = self.world.macros[mc.macro_id].body;
        let r = self.visit_int(ctx, body);
        for _ in 0..pushed {
            self.binders.pop();
        }
        r
    }

    /// Replays a phase-8 `$`-metamodel **ground expansion** as a formula
    /// (mt-107 P3, [`als_types::MetaExpansion`]): `all`/`some` over a `one`-of
    /// meta-typed bound is not a quantifier at all, but a fold of the body
    /// re-resolved once per meta atom.
    ///
    /// Each term is `atom in bound implies body` (`All`) or `atom in bound and
    /// body` (`Some`); the empty fold is `true` / `false`. The expansion
    /// introduces no quantifier, so the body keeps the *polarity* of the node
    /// the expansion replaced — but it does sit under the real `and`/`or`/
    /// `implies` connectives the fold emits, which is what decides
    /// skolemization (see the `blocked` computation below).
    fn replay_meta_formula(
        &mut self,
        ctx: Ctx,
        me: &als_types::MetaExpansion,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        debug_assert!(
            !matches!(me.fold, als_types::MetaFold::Comprehension),
            "comprehension fold reached the formula replay"
        );
        // The decl bound was resolved exactly once, into the enclosing table, so
        // it lowers once against the OUTER context and is shared by every term.
        let bound_rel = self.lower_bound_expr_set(ctx, me.bound)?;

        // mt-055 / §10.6, applied to the tree this fold actually builds: a
        // positive `or`/`implies` and a negated `and` each block skolemization
        // for their whole subtree. An `All` term is `guard implies body`
        // (blocks when positive) chained with `and` (blocks when negated); a
        // `Some` term is `guard and body` (blocks when negated) chained with
        // `or` (blocks when positive). The chain only exists from two bindings
        // on, which is the single-binding asymmetry below.
        let saved = self.pol;
        let chained = me.bindings.len() >= 2;
        let is_all = matches!(me.fold, als_types::MetaFold::All);
        self.pol.blocked = saved.blocked
            || if is_all {
                saved.positive || chained
            } else {
                !saved.positive || chained
            };
        let folded = self.meta_formula_fold(ctx, me, is_all, bound_rel, span);
        self.pol = saved;
        folded
    }

    /// The fold loop of [`Self::replay_meta_formula`], split out so the caller
    /// owns the [`Self::pol`] save/restore across every exit.
    fn meta_formula_fold(
        &mut self,
        ctx: Ctx,
        me: &als_types::MetaExpansion,
        is_all: bool,
        bound_rel: RelExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        let mut acc: Option<FormulaId> = None;
        for binding in &me.bindings {
            let (guard, body_ctx, _atom_rel) =
                self.meta_binding_parts(ctx, me, binding, bound_rel, span)?;
            let body = self.lower_formula(body_ctx, me.body);
            self.binders.pop();
            let body = body?;
            let term = if is_all {
                self.mk_formula(
                    FormulaKind::Implies {
                        antecedent: guard,
                        consequent: body,
                    },
                    span,
                )
            } else {
                self.mk_formula(FormulaKind::And(vec![guard, body]), span)
            };
            // The reference accumulates each new term on the LEFT of what it
            // already has (`answer = term.and(answer)`), so the tree for atoms
            // `a₁…aₙ` is `tₙ ∘ (tₙ₋₁ ∘ (… ∘ t₁))`. Binary nodes, not one n-ary
            // node, so the shape matches.
            acc = Some(match acc {
                None => term,
                Some(prev) if is_all => self.mk_formula(FormulaKind::And(vec![term, prev]), span),
                Some(prev) => self.mk_formula(FormulaKind::Or(vec![term, prev]), span),
            });
        }
        // The empty fold: `true` for `all`, `false` for `some`.
        Ok(acc.unwrap_or_else(|| self.mk_formula(FormulaKind::Const(is_all), span)))
    }

    /// The comprehension arm of [`Self::replay_meta_formula`]: the body is still
    /// a *formula* (a condition), and each term contributes the atom itself when
    /// the guard and the condition both hold — `(atom in bound and body) => atom
    /// else none`. The union of those, or `none` of arity 1 when nothing bound.
    fn replay_meta_rel(
        &mut self,
        ctx: Ctx,
        me: &als_types::MetaExpansion,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        debug_assert!(
            matches!(me.fold, als_types::MetaFold::Comprehension),
            "a formula fold reached the comprehension replay"
        );
        let bound_rel = self.lower_bound_expr_set(ctx, me.bound)?;
        // Each condition ends up inside a relational if-then-else, the same
        // non-monotone context `lower_rel`'s own ITE arm blocks skolemization
        // in (§10.6).
        let saved = self.pol;
        self.pol.blocked = true;
        let folded = self.meta_rel_fold(ctx, me, bound_rel, span);
        self.pol = saved;
        folded
    }

    /// The fold loop of [`Self::replay_meta_rel`], split out so the caller owns
    /// the [`Self::pol`] save/restore across every exit.
    fn meta_rel_fold(
        &mut self,
        ctx: Ctx,
        me: &als_types::MetaExpansion,
        bound_rel: RelExprId,
        span: Span,
    ) -> Result<RelExprId, TranslateError> {
        let mut acc: Option<RelExprId> = None;
        for binding in &me.bindings {
            let (guard, body_ctx, atom_rel) =
                self.meta_binding_parts(ctx, me, binding, bound_rel, span)?;
            let cond = self.lower_formula(body_ctx, me.body);
            self.binders.pop();
            let cond = self.mk_formula(FormulaKind::And(vec![guard, cond?]), span);
            let none = self.none_of_arity(1, span);
            let term = self.mk_rel(
                RelExprKind::IfThenElse {
                    cond,
                    then_branch: atom_rel,
                    else_branch: none,
                },
                span,
            );
            acc = Some(match acc {
                None => term,
                Some(prev) => self.mk_rel(
                    RelExprKind::Binary {
                        op: RelBinOp::Union,
                        lhs: term,
                        rhs: prev,
                    },
                    span,
                ),
            });
        }
        // The empty fold: `none` of arity 1.
        Ok(match acc {
            Some(r) => r,
            None => self.none_of_arity(1, span),
        })
    }

    /// One binding's shared preamble: the `atom in bound` guard, the context the
    /// body lowers under, and the atom's own denotation. **Pushes the binder** —
    /// the caller lowers the body and pops it, so a failing body still unwinds.
    ///
    /// The body's `ExprId`s live in the expansion node's own arena, so the
    /// context keeps `ctx`'s module and arena and swaps only the choice table:
    /// each binding carries its own sibling sub-table, keyed by the same
    /// `(ModuleId, ExprId)` pairs as its siblings.
    fn meta_binding_parts<'c>(
        &mut self,
        ctx: Ctx<'c>,
        me: &als_types::MetaExpansion,
        binding: &'c als_types::MetaBinding,
        bound_rel: RelExprId,
        span: Span,
    ) -> Result<(FormulaId, Ctx<'c>, RelExprId), TranslateError> {
        let atom_rel = self.sig_denote(binding.atom, span)?;
        let guard = self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: atom_rel,
                rhs: bound_rel,
            },
            span,
        );
        // The variable is ground — it denotes exactly one atom — so it binds as
        // an expression, never as a quantified `Var` (and so never skolemizes).
        self.binders.push((me.var.clone(), Binding::Expr(atom_rel)));
        let body_ctx = Ctx {
            module: ctx.module,
            choices: &binding.choices,
            ast: ctx.ast,
        };
        Ok((guard, body_ctx, atom_rel))
    }

    /// Binds a macro's parameters to its lowered arguments.
    ///
    /// `caller` is the context the macro USE sits in, and the arguments are
    /// lowered in it — not in a freshly-built module context. That distinction
    /// is the whole of mt-097 family B: a macro applied inside **another
    /// macro's body** has arguments that are the outer macro's parameters, and
    /// the checker recorded their choices in the outer macro's *nested* table
    /// (`expand_macro` resolves the argument expressions in its own `sub`
    /// context before recursing). Rebuilding a module-level context here dropped
    /// that table, so the argument name had no recorded resolution and lowering
    /// deferred — `overlapping-ranges[0]`, `philosophers[0]`/`[1]`. For a
    /// top-level macro use the caller's context IS the module context, so this
    /// is identical to the old behaviour there.
    fn bind_macro(
        &mut self,
        caller: Ctx,
        mc: &als_types::MacroChoice,
        span: Span,
    ) -> Result<usize, TranslateError> {
        let arg_ctx = Ctx {
            module: mc.arg_module,
            choices: caller.choices,
            ast: caller.ast,
        };
        let params = self.world.macros[mc.macro_id].params.clone();
        if params.len() != mc.args.len() {
            return Err(TranslateError::LoweringUnsupported {
                what: "macro arity mismatch".to_owned(),
                span,
            });
        }
        // A higher-order (lean) macro binds each callable-by-name parameter to its
        // recorded callable (`param[args]` inlines the real call); every other
        // parameter is an ordinary relational argument (mt-040). A callable
        // parameter the checker could not pin (not in `callables`) has no relation
        // value, so `lower_rel` below defers it typed. Compute every binding before
        // pushing so an argument that defers leaves the binder stack unchanged.
        let mut bindings: Vec<(String, Binding)> = Vec::with_capacity(params.len());
        for (i, name) in params.iter().enumerate() {
            let b = if let Some((_, c)) = mc.callables.iter().find(|(j, _)| *j == i) {
                Binding::Callable(c.clone())
            } else {
                Binding::Expr(self.lower_rel(arg_ctx, mc.args[i])?)
            };
            bindings.push((name.clone(), b));
        }
        let pushed = bindings.len();
        self.binders.extend(bindings);
        Ok(pushed)
    }

    /// A builtin box-join in formula position: `disj[…]` / `pred/totalOrder[…]`.
    fn lower_builtin_formula(
        &mut self,
        ctx: Ctx,
        op: BuiltinCall,
        e: ExprId,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        let args = self.box_args(ctx, e, span)?;
        match op {
            BuiltinCall::Disj => {
                // Staged pairwise disjointness (translation-ref §2.2):
                // `no(a&b) ∧ no((a+b)&c) ∧ …`.
                let mut rels = Vec::with_capacity(args.len());
                for &a in &args {
                    rels.push(self.lower_rel(ctx, a)?);
                }
                let mut parts: Vec<FormulaId> = Vec::new();
                let mut acc: Option<RelExprId> = None;
                for r in rels {
                    if let Some(prev) = acc {
                        let inter = self.mk_rel(
                            RelExprKind::Binary {
                                op: RelBinOp::Intersect,
                                lhs: prev,
                                rhs: r,
                            },
                            span,
                        );
                        parts.push(self.mk_formula(
                            FormulaKind::MultTest {
                                test: MultTest::No,
                                expr: inter,
                            },
                            span,
                        ));
                        acc = Some(self.mk_rel(
                            RelExprKind::Binary {
                                op: RelBinOp::Union,
                                lhs: prev,
                                rhs: r,
                            },
                            span,
                        ));
                    } else {
                        acc = Some(r);
                    }
                }
                if parts.is_empty() {
                    Ok(self.mk_formula(FormulaKind::Const(true), span))
                } else {
                    Ok(self.conjoin(parts, span))
                }
            }
            BuiltinCall::TotalOrder => {
                // `pred/totalOrder[elem, first, next]` (translation-ref §5/§2.2,
                // LEDGER-004): the hand-built total-order formula the reference's
                // non-native path uses, semantically equivalent to Kodkod's native
                // `ord[next, elem, first, last]`. `next` is the immediate-successor
                // relation of a single linear chain over `elem`, `first` its minimum.
                // Exactly the `n!` orderings over a fixed `elem` of size `n` satisfy
                // it, so the enumerated count matches the jar's sym0 column whenever
                // the ordered sig has a genuine partition choice (bounds pinning does
                // not engage — probes T14a-e). When pinning *does* engage
                // (bounds_builder), `first`/`next` are exact constants and this
                // formula is trivially satisfied.
                if args.len() != 3 {
                    return Err(TranslateError::LoweringUnsupported {
                        what: "`pred/totalOrder` with other than 3 arguments".to_owned(),
                        span,
                    });
                }
                let elem = self.lower_rel(ctx, args[0])?;
                let first = self.lower_rel(ctx, args[1])?;
                let next = self.lower_rel(ctx, args[2])?;
                Ok(self.total_order_formula(elem, first, next, span))
            }
            BuiltinCall::IntCast | BuiltinCall::IntAtom => {
                Err(TranslateError::LoweringUnsupported {
                    what: "int cast in a formula position".to_owned(),
                    span,
                })
            }
        }
    }

    // ============================ sort classification ============================

    /// The sort of expression `e` (translation-ref §2), from the recorded
    /// choices — used only to route `=`/`in` (int special case) and small-int
    /// promotion; never a re-derivation of the type checker.
    fn sort_of(&self, ctx: Ctx, e: ExprId) -> Sort {
        match &self.ast_of(ctx).exprs[e].kind {
            ExprKind::Num(_) => Sort::Int,
            ExprKind::Str(_) | ExprKind::Const(_) | ExprKind::This => Sort::Rel,
            ExprKind::Unary { op, expr } => match op {
                UnOp::Card | UnOp::IntOf | UnOp::SumOf => Sort::Int,
                UnOp::Not
                | UnOp::No
                | UnOp::Some
                | UnOp::Lone
                | UnOp::One
                | UnOp::Always
                | UnOp::Eventually
                | UnOp::After
                | UnOp::Before
                | UnOp::Historically
                | UnOp::Once => Sort::Formula,
                _ => self.sort_of(ctx, *expr),
            },
            ExprKind::Binary { op, lhs, rhs } => match op {
                BinOp::Or
                | BinOp::And
                | BinOp::Iff
                | BinOp::Implies
                | BinOp::Until
                | BinOp::Releases
                | BinOp::Since
                | BinOp::Triggered
                | BinOp::Seq => Sort::Formula,
                BinOp::Shl
                | BinOp::Sha
                | BinOp::Shr
                | BinOp::IntAdd
                | BinOp::IntSub
                | BinOp::IntMul
                | BinOp::IntDiv
                | BinOp::IntRem => Sort::Int,
                BinOp::Join => self.spine_sort(ctx, e),
                // The `MINUS` peephole returns an `IntConstant` — an
                // `IntExpression`, not an `Expression` — so a folding
                // `0-(max+1)` is int-sorted wherever the jar dispatches on the
                // translated Kodkod class, which no other `-` ever is. That is
                // load-bearing in three places beyond the value itself:
                // [`Self::lower_rel`]'s guard re-wraps it as `Int[min]`
                // (the jar's `toSet` → `.toExpression()`); the ITE dispatch
                // reads it through [`Self::ite_sort`] and takes the int branch,
                // dragging the else branch with it (`no F => (0-8) else 1`
                // renders bare `1`); and the evaluator console renders it bare
                // (`-8`, not `{-8}`) through [`Self::fragment_sort_in`].
                // See [`Self::minus_folds_to_min`].
                BinOp::Diff if self.minus_folds_to_min(ctx, *op, *lhs, *rhs) => Sort::Int,
                _ => Sort::Rel,
            },
            ExprKind::BoxJoin { .. } => self.spine_sort(ctx, e),
            ExprKind::Name(_) | ExprKind::AtName(_) => self.name_sort(ctx, e),
            ExprKind::Arrow { .. } | ExprKind::Comprehension { .. } => Sort::Rel,
            ExprKind::Compare { .. } => Sort::Formula,
            ExprKind::IfThenElse { then_branch, .. } => self.ite_sort(ctx, *then_branch),
            ExprKind::Quant { quant, .. } => {
                if matches!(quant, Quant::Sum) {
                    Sort::Int
                } else {
                    Sort::Formula
                }
            }
            ExprKind::Let { body, .. } => self.sort_of(ctx, *body),
            // A single-element block `{ e }` (a fun body) has `e`'s sort.
            ExprKind::Block(exprs) if exprs.len() == 1 => self.sort_of(ctx, exprs[0]),
            ExprKind::Block(_) => Sort::Formula,
        }
    }

    /// The sort an `if-then-else` takes, read off its **then** branch alone
    /// (translation-ref §10.7g, mt-095 probes i1/i2, i5, m2/m4).
    ///
    /// `visit(ExprITE)` tests the *then* branch's translated Kodkod class and
    /// coerces the else branch to match (`cform`/`cset`/`cint`) — the else
    /// branch never votes. The one place mettle's `sort_of` disagrees with that
    /// class is a bare numeral: `visit(ExprConstant)` case `NUMBER` is
    /// `IntConstant.constant(n).toExpression()`, an `IntToExprCast`, which is an
    /// `Expression` — and `instanceof Expression` is tested *before*
    /// `instanceof IntExpression`, so a numeral branch makes the ITE relational.
    ///
    /// Everywhere else a numeral behaves int-sorted anyway, because `toInt`
    /// unwraps an `IntToExprCast` back to its `IntExpression` (mettle's
    /// `IntToAtom` peephole in `lower_int`) — the ITE dispatch is the sole
    /// position where the distinction is observable.
    fn ite_sort(&self, ctx: Ctx, then_branch: ExprId) -> Sort {
        match &self.ast_of(ctx).exprs[then_branch].kind {
            ExprKind::Num(_) => Sort::Rel,
            _ => self.sort_of(ctx, then_branch),
        }
    }

    /// The sort the **evaluator console's own top-level dispatch** gives a
    /// fragment's root (evaluator contract §3, probes E-60–E-79).
    ///
    /// A different question from [`Self::sort_of`]'s, which routes coercions
    /// *inside* an expression and is the solve path's classifier too — hence a
    /// separate walk rather than an edit to that one. Here the question is only
    /// "does this root translate to a Kodkod `IntExpression`", because that is
    /// the sole branch of `A4Solution.eval` that renders a bare numeral; an
    /// `Expression` becomes an `A4TupleSet` and prints `{n}`.
    ///
    /// Three int-*typed* forms translate to an `Expression` and so render
    /// `{n}` here where [`Self::sort_of`] says `Int`:
    ///
    /// - a **numeral literal** — `visit(ExprConstant)` NUMBER is
    ///   `IntConstant.constant(n).toExpression()`, the same fact mt-095 pinned
    ///   for the ITE dispatch (probes E-60–E-64; out-of-range literals wrap
    ///   two's-complement and still render `{n}`, E-63/E-64);
    /// - **`int[e]` / `sum[e]` / `int e` / `sum e`** — `CAST2INT`, which the
    ///   evaluator's re-resolve re-wraps as `Int[int[e]]` (probes E-70–E-73).
    ///
    /// And symmetrically, a user-written **`Int[e]`** is *dropped* by that same
    /// re-resolve, so it is transparent rather than relational (E-74/E-75) —
    /// `Int[#A]` renders bare `1`.
    ///
    /// `let` is transparent because the reference's `visit(ExprLet)` substitutes
    /// (the body's own translation is the result), so a body that is just the
    /// bound name takes the binding's shape (E-76/E-77).
    ///
    /// Only the rendered *shape* moves: [`Self::lower_rel`] and
    /// [`Self::lower_int`] each open with the coercion guard for the other sort,
    /// so both dispatches compute the same value.
    fn fragment_sort(&self, ctx: Ctx, e: ExprId) -> Sort {
        self.fragment_sort_in(ctx, e, &mut Vec::new())
    }

    /// [`Self::fragment_sort`] carrying the enclosing `let` bindings, innermost
    /// last, so a body that is just a bound name can be followed to its value.
    fn fragment_sort_in(&self, ctx: Ctx, e: ExprId, lets: &mut Vec<(String, ExprId)>) -> Sort {
        match &self.ast_of(ctx).exprs[e].kind {
            ExprKind::Num(_) => Sort::Rel,
            ExprKind::Unary { op, expr } => match op {
                UnOp::Card => Sort::Int,
                UnOp::IntOf | UnOp::SumOf => Sort::Rel,
                UnOp::Not
                | UnOp::No
                | UnOp::Some
                | UnOp::Lone
                | UnOp::One
                | UnOp::Always
                | UnOp::Eventually
                | UnOp::After
                | UnOp::Before
                | UnOp::Historically
                | UnOp::Once => Sort::Formula,
                _ => self.fragment_sort_in(ctx, *expr, lets),
            },
            ExprKind::Binary {
                op: BinOp::Join, ..
            } => self.fragment_spine_sort(ctx, e, lets),
            ExprKind::BoxJoin { .. } => self.fragment_spine_sort(ctx, e, lets),
            ExprKind::Name(_) | ExprKind::AtName(_) => self.fragment_name_sort(ctx, e, lets),
            ExprKind::IfThenElse { then_branch, .. } => {
                // The else branch never votes (mt-095): `visit(ExprITE)` reads
                // the then branch's translated class and coerces the else one to
                // match. Probe E-78: `(some A => int[3] else 0)` is `{3}`.
                self.fragment_sort_in(ctx, *then_branch, lets)
            }
            ExprKind::Let { bindings, body } => {
                let depth = lets.len();
                for b in bindings {
                    lets.push((b.name.text.clone(), b.value));
                }
                let sort = self.fragment_sort_in(ctx, *body, lets);
                lets.truncate(depth);
                sort
            }
            ExprKind::Block(exprs) if exprs.len() == 1 => {
                self.fragment_sort_in(ctx, exprs[0], lets)
            }
            // Everything left — a formula, a comprehension, an arrow, a
            // `sum`/other quantifier, a string or constant — is classified the
            // same either way, so there is one rule for it, not two.
            _ => self.sort_of(ctx, e),
        }
    }

    fn fragment_name_sort(&self, ctx: Ctx, e: ExprId, lets: &[(String, ExprId)]) -> Sort {
        match self.choice(ctx, e) {
            Some(ExprChoice::Name(NameChoice::Var(v))) => {
                // Innermost wins, and the binding is classified against only the
                // bindings *outside* it — which also makes the recursion
                // terminate under shadowing (`let x = 1 | let x = x | x`).
                match lets.iter().rposition(|(name, _)| name == v) {
                    Some(i) => {
                        let value = lets[i].1;
                        self.fragment_sort_in(ctx, value, &mut lets[..i].to_vec())
                    }
                    // A quantifier/comprehension binder or an instance atom
                    // global: relational, as `name_sort` also says.
                    None => Sort::Rel,
                }
            }
            Some(ExprChoice::Name(NameChoice::Macro(mc))) => self.fragment_macro_sort(mc),
            _ => self.name_sort(ctx, e),
        }
    }

    fn fragment_spine_sort(&self, ctx: Ctx, e: ExprId, lets: &mut Vec<(String, ExprId)>) -> Sort {
        match self.choice(ctx, e) {
            Some(ExprChoice::Spine(SpineChoice::Builtin {
                op: BuiltinCall::IntCast,
            })) => Sort::Rel,
            Some(ExprChoice::Spine(SpineChoice::Builtin {
                op: BuiltinCall::IntAtom,
            })) => {
                let span = self.ast_of(ctx).exprs[e].span;
                match self.first_box_arg(ctx, e, span) {
                    Ok(arg) => self.fragment_sort_in(ctx, arg, lets),
                    Err(_) => Sort::Rel,
                }
            }
            Some(ExprChoice::Spine(SpineChoice::Macro(mc))) => self.fragment_macro_sort(mc),
            _ => self.spine_sort(ctx, e),
        }
    }

    /// A macro call is inlined by the reference's `visit(ExprCall)`, so the
    /// body's own translated class is what reaches the dispatch. The body lives
    /// in its own module and choice table, so it starts with a fresh `let` env.
    fn fragment_macro_sort(&self, mc: &als_types::MacroChoice) -> Sort {
        let ctx = Ctx {
            module: mc.body_module,
            choices: &mc.body_choices,
            ast: None,
        };
        self.fragment_sort_in(ctx, self.world.macros[mc.macro_id].body, &mut Vec::new())
    }

    fn name_sort(&self, ctx: Ctx, e: ExprId) -> Sort {
        match self.choice(ctx, e) {
            Some(ExprChoice::Name(NameChoice::Call0(func))) => self.func_sort(*func),
            Some(ExprChoice::Name(NameChoice::Macro(mc))) => self.macro_sort(mc),
            _ => Sort::Rel,
        }
    }

    fn spine_sort(&self, ctx: Ctx, e: ExprId) -> Sort {
        match self.choice(ctx, e) {
            Some(ExprChoice::Spine(SpineChoice::Call(cc))) => self.func_sort(cc.func),
            Some(ExprChoice::Spine(SpineChoice::Builtin { op })) => match op {
                BuiltinCall::IntCast => Sort::Int,
                BuiltinCall::IntAtom => Sort::Rel,
                BuiltinCall::Disj | BuiltinCall::TotalOrder => Sort::Formula,
            },
            Some(ExprChoice::Spine(SpineChoice::Macro(mc))) => self.macro_sort(mc),
            _ => Sort::Rel,
        }
    }

    fn func_sort(&self, func: FuncIdx) -> Sort {
        let f = &self.world.funcs[func];
        if f.is_pred {
            Sort::Formula
        } else if f.return_ty.is_small_int {
            Sort::Int
        } else {
            Sort::Rel
        }
    }

    fn macro_sort(&self, mc: &als_types::MacroChoice) -> Sort {
        let ctx = Ctx {
            module: mc.body_module,
            choices: &mc.body_choices,
            ast: None,
        };
        self.sort_of(ctx, self.world.macros[mc.macro_id].body)
    }

    // ============================ small helpers ============================

    fn ctx(&self, module: ModuleId) -> Ctx<'a> {
        Ctx {
            module,
            choices: &self.world.choices,
            ast: None,
        }
    }

    /// The arena a context's `ExprId`s index into: its module's loaded AST, or
    /// the standalone fragment's own ([`Ctx::ast`]).
    fn ast_of<'b>(&self, ctx: Ctx<'b>) -> &'b Ast
    where
        'a: 'b,
    {
        match ctx.ast {
            Some(ast) => ast,
            None => self.ast(ctx.module),
        }
    }

    fn ast(&self, module: ModuleId) -> &'a Ast {
        let file = self.graph.modules[module].file;
        self.graph.files.file(file).ast_ref()
    }

    fn choice<'c>(&self, ctx: Ctx<'c>, e: ExprId) -> Option<&'c ExprChoice> {
        ctx.choices.get(ctx.module, e)
    }

    fn span_of(&self, ctx: Ctx, e: ExprId) -> Span {
        self.ast_of(ctx).exprs[e].span
    }

    fn sig_denote(&mut self, sig: SigId, span: Span) -> Result<RelExprId, TranslateError> {
        self.bounds.sig_denote.get(&sig).copied().ok_or_else(|| {
            TranslateError::LoweringUnsupported {
                what: format!("sig `{}` has no denotation", self.world.sigs[sig].name),
                span,
            }
        })
    }

    /// The jar's **live universe** as a relation expression (mt-053, LEDGER-011):
    /// the union, in `SigId` order, of every top-level prim sig's *denotation* —
    /// i.e. each direct child of the root `univ` (`Int`, `String`, and every
    /// user top-level sig). Because each sig denote is itself a relation whose
    /// value tracks that sig's *current* population per candidate instance
    /// (`⋃children + remainder`), the union is genuinely dynamic: an
    /// allocated-but-empty non-exact sig's atoms drop out of `univ` in exactly
    /// the instances where the sig doesn't contain them (probe rows 4/7). `Int`
    /// and `String` atoms (padding included) are always present (their builtin
    /// relations are exact constants — probe rows 2/3). Subset (`in`) and
    /// `extends` children contribute nothing extra: they are already covered by
    /// their prim parent's population (idempotent union — probe row 5).
    ///
    /// `none` is excluded (its denote is the empty `RelConst::None`, contributing
    /// nothing). `seq/Int` is excluded (its prim parent is `Int`, not `univ`).
    fn live_univ(&mut self, span: Span) -> RelExprId {
        let univ = self.world.builtins.univ;
        let none = self.world.builtins.none;
        let parts: Vec<RelExprId> = self
            .world
            .sigs
            .iter()
            .filter(|(id, s)| {
                *id != none
                    && matches!(&s.kind, als_types::SigKind::Prim { parent: Some(p) } if *p == univ)
            })
            .map(|(id, s)| {
                // The mt-030 denote seam is total over sigs; a missing denote
                // here would silently shrink `univ` (a wrong-verdict shape),
                // so it is an invariant violation, never a skip (STYLE I1).
                *self
                    .bounds
                    .sig_denote
                    .get(&id)
                    .unwrap_or_else(|| panic!("no denote for top-level sig {}", s.name))
            })
            .collect();
        self.union_rel(&parts, span)
    }

    /// `iden` in user-expression position: the identity relation restricted to
    /// the [live universe](Self::live_univ) — `iden & (live -> live)` — so it
    /// tracks the same dynamic per-instance liveness as `univ` (mt-053,
    /// LEDGER-011; probe row 6b). The all-atoms `RelConst::Iden` is intersected
    /// down to `{(a, a) | a ∈ live}`.
    fn live_iden(&mut self, span: Span) -> RelExprId {
        let live = self.live_univ(span);
        let iden = self.mk_rel(RelExprKind::Const(RelConst::Iden), span);
        let square = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Product,
                lhs: live,
                rhs: live,
            },
            span,
        );
        self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Intersect,
                lhs: iden,
                rhs: square,
            },
            span,
        )
    }

    /// Folds a non-empty slice of same-arity relation expressions into a
    /// left-nested union, deterministically (source/`SigId` order). An empty
    /// slice cannot arise for [`Self::live_univ`] (`Int`/`String` are always
    /// present); guarded to the empty unary relation for totality.
    fn union_rel(&mut self, parts: &[RelExprId], span: Span) -> RelExprId {
        let mut iter = parts.iter().copied();
        let Some(first) = iter.next() else {
            return self.mk_rel(RelExprKind::Const(RelConst::None), span);
        };
        iter.fold(first, |acc, next| {
            self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Union,
                    lhs: acc,
                    rhs: next,
                },
                span,
            )
        })
    }

    /// Lowers each `let` binding value in its own sort and pushes it onto the
    /// binder stack (innermost last), returning how many were pushed so the
    /// caller can pop them after the body. Referential transparency: the value
    /// is lowered once here, in the enclosing env, and its IR node is reused at
    /// every use of the name (translation-ref §2 — the jar binds it once in the
    /// Kodkod env, no re-evaluation).
    ///
    /// A formula-valued binding (`let p = some a | p …`, including the
    /// `c => f else g` formula-ITE spelling) becomes a [`Binding::Formula`], so a
    /// use in formula position consumes it directly; every other sort lowers via
    /// `lower_rel`. Int values need no special case — `lower_rel`'s `Int[·]`
    /// cast guard wraps them and the symmetric `int[·]` guard unwraps them at the
    /// use site, so an int-valued `let` round-trips as a `Binding::Expr` exactly
    /// as before this seam existed.
    fn push_let_bindings(
        &mut self,
        ctx: Ctx,
        bindings: &[LetBinding],
    ) -> Result<usize, TranslateError> {
        let mut pushed = 0;
        for b in bindings {
            let is_formula = self.sort_of(ctx, b.value) == Sort::Formula
                || self.name_bound_to_formula(ctx, b.value);
            let binding = if is_formula {
                // Deliberately NOT lowered here — see [`Binding::Formula`].
                Binding::Formula {
                    expr: b.value,
                    module: ctx.module,
                    depth: self.binders.len(),
                }
            } else {
                Binding::Expr(self.lower_rel(ctx, b.value)?)
            };
            self.binders.push((b.name.text.clone(), binding));
            pushed += 1;
        }
        Ok(pushed)
    }

    /// Whether `e` is a bare name already bound to a formula-valued `let`
    /// (mt-056): the `let q = p | …` rebinding, probe cell `n01`. `sort_of`
    /// reads the recorded choice table, which classifies a `let` binder as an
    /// ordinary `Var` (relational) — it has no idea the binding is a formula —
    /// so without this the rebinding takes the `lower_rel` path and defers
    /// typed where the jar simply counts (15 / 8).
    fn name_bound_to_formula(&self, ctx: Ctx, e: ExprId) -> bool {
        let Some(ExprChoice::Name(NameChoice::Var(name))) = self.choice(ctx, e) else {
            return false;
        };
        self.binders
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .is_some_and(|(_, b)| matches!(b, Binding::Formula { .. }))
    }

    /// The formula bound to a formula-valued `let` name (translation-ref §2). A
    /// name that is instead relation- or int-valued reaching formula position is
    /// a checker type error, so it is a typed defer, never a wrong verdict.
    fn lookup_binder_formula(
        &mut self,
        ctx: Ctx,
        name: &str,
        span: Span,
    ) -> Result<FormulaId, TranslateError> {
        let found = self
            .binders
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, b)| match b {
                Binding::Formula {
                    expr,
                    module,
                    depth,
                } => Some((*expr, *module, *depth)),
                _ => None,
            });
        let Some(bound) = found else {
            return Err(TranslateError::LoweringUnsupported {
                what: format!("unbound variable `{name}`"),
                span,
            });
        };
        let Some((expr, module, depth)) = bound else {
            return Err(TranslateError::LoweringUnsupported {
                what: format!("non-formula binding `{name}` used in a formula position"),
                span,
            });
        };
        if module != ctx.module {
            return Err(TranslateError::LoweringUnsupported {
                what: format!("formula-valued let `{name}` used from another module's context"),
                span,
            });
        }
        // Lower the RHS HERE, so the §10.6 connective rule sees this use's
        // ambient polarity (`self.pol` is the use site's) — but under the
        // BINDING site's binder stack, so an intervening shadowing binder cannot
        // capture a free name of the RHS (mt-056, translation-ref §10.6a).
        // `lower_formula` leaves the stack balanced, so the tail restores exactly.
        let tail = self.binders.split_off(depth);
        let lowered = self.lower_formula(ctx, expr);
        self.binders.extend(tail);
        lowered
    }

    fn lookup_binder(&mut self, name: &str, span: Span) -> Result<RelExprId, TranslateError> {
        for (n, b) in self.binders.iter().rev() {
            if n == name {
                return match b {
                    Binding::Var(vid) => {
                        let vid = *vid;
                        Ok(self.mk_rel(RelExprKind::Var(vid), span))
                    }
                    Binding::Expr(id) => Ok(*id),
                    // A formula-valued `let` binding has no relational value; a
                    // use in relation position is a checker type error, so defer
                    // typed here rather than fabricate one (translation-ref §2;
                    // consumed in formula position by `lookup_binder_formula`).
                    Binding::Formula { .. } => Err(TranslateError::LoweringUnsupported {
                        what: format!("formula-valued let `{name}` used in a relation position"),
                        span,
                    }),
                    // A higher-order-macro callable parameter has no relational
                    // value; it is only meaningful applied (`param[args]`), handled
                    // by `callable_head` before this lookup (mt-040).
                    Binding::Callable(_) => Err(TranslateError::LoweringUnsupported {
                        what: format!("callable parameter `{name}` used as a value"),
                        span,
                    }),
                };
            }
        }
        Err(TranslateError::LoweringUnsupported {
            what: format!("unbound variable `{name}`"),
            span,
        })
    }

    /// The callable bound to `name` (innermost-first), if it is a higher-order
    /// macro's callable-by-name parameter (mt-040).
    fn lookup_callable(&self, name: &str) -> Option<als_types::CallableChoice> {
        self.binders.iter().rev().find_map(|(n, b)| match b {
            Binding::Callable(c) if n == name => Some(c.clone()),
            _ => None,
        })
    }

    /// If `e` is an application of a higher-order-macro callable parameter
    /// (`param` or `param[args]`), returns the callable and its argument exprs
    /// (mt-040). Only a bare-name head bound to a [`Binding::Callable`] matches.
    fn callable_head(
        &self,
        ctx: Ctx,
        e: ExprId,
    ) -> Option<(als_types::CallableChoice, Vec<ExprId>)> {
        match &self.ast_of(ctx).exprs[e].kind {
            ExprKind::Name(qn) => {
                let [seg] = qn.segments.as_slice() else {
                    return None;
                };
                self.lookup_callable(&seg.text).map(|c| (c, Vec::new()))
            }
            ExprKind::BoxJoin { target, args } => {
                let ExprKind::Name(qn) = &self.ast_of(ctx).exprs[*target].kind else {
                    return None;
                };
                let [seg] = qn.segments.as_slice() else {
                    return None;
                };
                self.lookup_callable(&seg.text).map(|c| (c, args.clone()))
            }
            _ => None,
        }
    }

    fn lower_this(&mut self, span: Span) -> Result<RelExprId, TranslateError> {
        self.lookup_binder("this", span)
    }

    /// The arity of a lowered relation expression, read off the IR (used for
    /// `<:`/`:>` padding). Total by construction over the relational IR.
    fn ir_arity(&self, r: RelExprId) -> Option<usize> {
        match &self.ir.rel_exprs[r].kind {
            RelExprKind::Relation(rel) => Some(self.ir.relations[*rel].arity),
            RelExprKind::Var(v) => Some(self.ir.vars[*v].arity),
            RelExprKind::Const(RelConst::None | RelConst::Univ) => Some(1),
            RelExprKind::Const(RelConst::Iden) => Some(2),
            RelExprKind::Binary { op, lhs, rhs } => {
                let a = self.ir_arity(*lhs)?;
                let b = self.ir_arity(*rhs)?;
                Some(match op {
                    RelBinOp::Join => a + b - 2,
                    RelBinOp::Product => a + b,
                    RelBinOp::Union | RelBinOp::Diff | RelBinOp::Intersect | RelBinOp::Override => {
                        a
                    }
                })
            }
            RelExprKind::Unary { op, expr } => match op {
                RelUnOp::Transpose | RelUnOp::Closure | RelUnOp::ReflexiveClosure => {
                    let _ = expr;
                    Some(2)
                }
            },
            RelExprKind::Prime(e) => self.ir_arity(*e),
            RelExprKind::IfThenElse { then_branch, .. } => self.ir_arity(*then_branch),
            RelExprKind::Comprehension { decls, .. } => {
                let mut n = 0;
                for d in decls {
                    n += self.ir.vars[d.var].arity;
                }
                Some(n)
            }
            RelExprKind::IntToAtom(_) => Some(1),
        }
    }

    fn none_of_arity(&mut self, k: usize, span: Span) -> RelExprId {
        let none = self.mk_rel(RelExprKind::Const(RelConst::None), span);
        let mut acc = none;
        for _ in 1..k.max(1) {
            let n = self.mk_rel(RelExprKind::Const(RelConst::None), span);
            acc = self.mk_rel(
                RelExprKind::Binary {
                    op: RelBinOp::Product,
                    lhs: acc,
                    rhs: n,
                },
                span,
            );
        }
        acc
    }

    fn conjoin(&mut self, parts: Vec<FormulaId>, span: Span) -> FormulaId {
        match parts.len() {
            0 => self.mk_formula(FormulaKind::Const(true), span),
            1 => parts[0],
            _ => self.mk_formula(FormulaKind::And(parts), span),
        }
    }

    fn not(&mut self, f: FormulaId, span: Span) -> FormulaId {
        self.mk_formula(FormulaKind::Not(f), span)
    }

    /// The hand-built `pred/totalOrder[elem, first, next]` formula (LEDGER-004,
    /// translation-ref §5/§2.2): `first` is the unique minimum, `next` is the
    /// functional/injective immediate-successor relation of a single acyclic
    /// chain that reaches all of `elem`. Its models are exactly the `n!`
    /// linear orders over a fixed `elem`, so it pins the enumerated count in the
    /// subsig partition-choice case where the bounds pinning does not engage.
    #[allow(
        clippy::too_many_lines,
        reason = "one pinned formula built clause by clause; splitting would scatter \
                  the LEDGER-004 shape across helpers"
    )]
    fn total_order_formula(
        &mut self,
        elem: RelExprId,
        first: RelExprId,
        next: RelExprId,
        span: Span,
    ) -> FormulaId {
        let mut parts: Vec<FormulaId> = Vec::with_capacity(5);
        // `one first`.
        parts.push(self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::One,
                expr: first,
            },
            span,
        ));
        // `no next.first` — `first` has no predecessor (rules out cycles).
        let pred_of_first = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: next,
                rhs: first,
            },
            span,
        );
        parts.push(self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::No,
                expr: pred_of_first,
            },
            span,
        ));
        // `all e: elem | lone e.next` — each element has ≤ 1 successor.
        let ev = self.ir.vars.alloc(Var {
            name: "totalOrder_e".to_owned(),
            arity: 1,
            span,
        });
        let ev_expr = self.mk_rel(RelExprKind::Var(ev), span);
        let e_next = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: ev_expr,
                rhs: next,
            },
            span,
        );
        let lone_succ = self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::Lone,
                expr: e_next,
            },
            span,
        );
        parts.push(self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: ev,
                bound: elem,
                body: lone_succ,
            },
            span,
        ));
        // `all e: elem | lone next.e` — each element has ≤ 1 predecessor.
        let pv = self.ir.vars.alloc(Var {
            name: "totalOrder_p".to_owned(),
            arity: 1,
            span,
        });
        let pv_expr = self.mk_rel(RelExprKind::Var(pv), span);
        let next_e = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: next,
                rhs: pv_expr,
            },
            span,
        );
        let lone_pred = self.mk_formula(
            FormulaKind::MultTest {
                test: MultTest::Lone,
                expr: next_e,
            },
            span,
        );
        parts.push(self.mk_formula(
            FormulaKind::Quant {
                kind: QuantKind::All,
                var: pv,
                bound: elem,
                body: lone_pred,
            },
            span,
        ));
        // `elem in first.*next` — every element is reachable from `first`.
        let star_next = self.mk_rel(
            RelExprKind::Unary {
                op: RelUnOp::ReflexiveClosure,
                expr: next,
            },
            span,
        );
        let reach = self.mk_rel(
            RelExprKind::Binary {
                op: RelBinOp::Join,
                lhs: first,
                rhs: star_next,
            },
            span,
        );
        parts.push(self.mk_formula(
            FormulaKind::RelCompare {
                op: RelCmpOp::Subset,
                lhs: elem,
                rhs: reach,
            },
            span,
        ));
        self.conjoin(parts, span)
    }

    fn mark_temporal(&mut self, op: &'static str, span: Span) {
        if self.temporal.is_none() {
            self.temporal = Some((op, span));
        }
    }

    fn mk_formula(&mut self, kind: FormulaKind, span: Span) -> FormulaId {
        self.ir.formulas.alloc(Formula { kind, span })
    }

    fn mk_rel(&mut self, kind: RelExprKind, span: Span) -> RelExprId {
        self.ir.rel_exprs.alloc(RelExpr { kind, span })
    }

    fn mk_int(&mut self, kind: IntExprKind, span: Span) -> IntExprId {
        self.ir.int_exprs.alloc(IntExpr { kind, span })
    }

    /// The single argument of a one-arg builtin box join (`int[e]`/`Int[e]`).
    fn first_box_arg(&self, ctx: Ctx, e: ExprId, span: Span) -> Result<ExprId, TranslateError> {
        match &self.ast_of(ctx).exprs[e].kind {
            ExprKind::BoxJoin { args, .. } if !args.is_empty() => Ok(args[0]),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "builtin cast with no argument".to_owned(),
                span,
            }),
        }
    }

    fn box_args(&self, ctx: Ctx, e: ExprId, span: Span) -> Result<Vec<ExprId>, TranslateError> {
        match &self.ast_of(ctx).exprs[e].kind {
            ExprKind::BoxJoin { args, .. } => Ok(args.clone()),
            _ => Err(TranslateError::LoweringUnsupported {
                what: "builtin form of unexpected shape".to_owned(),
                span,
            }),
        }
    }

    /// The value-arity of a decl bound (for the implicit-`one`): the arity of the
    /// bound expression's resolved type, from the sig/field it denotes. `1` for a
    /// unary sig/field-value; `None` if unknown (then no implicit `one`).
    fn rel_value_arity(&self, bound: ExprId, ctx: Ctx) -> Option<usize> {
        self.rel_arity(bound, ctx)
    }

    /// The arity of a relation expression, from the sig/field it denotes (for
    /// restriction padding and implicit `one`). Best-effort: known for a plain
    /// sig/field name; `None` for compounds (callers defer).
    fn rel_arity(&self, e: ExprId, ctx: Ctx) -> Option<usize> {
        match &self.ast_of(ctx).exprs[e].kind {
            ExprKind::Name(_) | ExprKind::AtName(_) => match self.choice(ctx, e)? {
                ExprChoice::Name(NameChoice::Sig(_)) => Some(1),
                ExprChoice::Name(NameChoice::Field {
                    field,
                    implicit_this,
                }) => {
                    let a = self.world.fields[*field].ty.arity()?;
                    Some(if *implicit_this { a - 1 } else { a })
                }
                _ => None,
            },
            ExprKind::Const(Const::Iden) => Some(2),
            ExprKind::Const(_) => Some(1),
            _ => None,
        }
    }

    fn find_func_para(&self, module: ModuleId, func: FuncIdx) -> Option<als_syntax::ast::ParaId> {
        let ast = self.ast(module);
        let name = &self.world.funcs[func].name;
        // Match the nth func/pred with this name to its FuncId is fragile; the
        // simplest correct link is the declaration order. Find by name + body.
        let body = self.world.funcs[func].body;
        for &p in &ast.paragraphs {
            match &ast.paras[p] {
                als_syntax::ast::Para::Pred(pr) if &pr.name.text == name && pr.body == body => {
                    return Some(p)
                }
                als_syntax::ast::Para::Fun(fu) if &fu.name.text == name && fu.body == body => {
                    return Some(p)
                }
                _ => {}
            }
        }
        None
    }
}

// A local alias so the many signatures read clearly.
type FuncIdx = als_types::FuncId;

/// A list of quantifier/`sum` variables with their (unary) bounds, in order.
type VarBounds = Vec<(crate::ir::VarId, RelExprId)>;

/// Whether higher-order decls in a decl list may be skolemized here
/// (translation-ref §10.6). `Denied` at an effective-universal quantifier, under a
/// blocked context, or in a comprehension — a HO decl then defers typed.
#[derive(Copy, Clone, PartialEq, Eq)]
enum SkolemRegime {
    Allowed,
    Denied,
}

/// The outcome of binding a decl list ([`Lowerer::bind_decls_vars`]): the
/// first-order `(var, bound)` pairs, their pairwise-disjointness guard, the
/// skolem decls' membership/multiplicity constraints, and the binder count.
#[derive(Default)]
struct BoundDecls {
    /// First-order `(var, bound)` pairs, in order (wrapped as nested quantifiers).
    fo: VarBounds,
    /// Pairwise disjointness of `disj`-marked first-order groups, if any.
    fo_disj: Option<FormulaId>,
    /// Membership/multiplicity/disjointness constraints of skolemized HO decls.
    skolem_constraints: Vec<FormulaId>,
    /// Count of pushed binders (to pop after the body).
    pushed: usize,
}

/// The Cartesian product of two tuple sets (arity a+b).
fn tupleset_product(a: &TupleSet, b: &TupleSet) -> TupleSet {
    let mut out = TupleSet::empty(a.arity() + b.arity());
    for ta in a.iter() {
        for tb in b.iter() {
            let mut atoms = ta.atoms().to_vec();
            atoms.extend_from_slice(tb.atoms());
            out.insert(Tuple::new(atoms));
        }
    }
    out
}

/// The union of two same-arity tuple sets (`None` on arity mismatch — a lowering
/// bug the type checker precludes).
fn tupleset_union(a: &TupleSet, b: &TupleSet) -> Option<TupleSet> {
    if a.arity() != b.arity() {
        return None;
    }
    let mut out = a.clone();
    for t in b.iter() {
        out.insert(t.clone());
    }
    Some(out)
}

/// The intersection of two same-arity tuple sets.
fn tupleset_intersect(a: &TupleSet, b: &TupleSet) -> Option<TupleSet> {
    if a.arity() != b.arity() {
        return None;
    }
    let mut out = TupleSet::empty(a.arity());
    for t in a.iter() {
        if b.contains(t) {
            out.insert(t.clone());
        }
    }
    Some(out)
}

/// The relational join of two tuple sets over the shared middle column (result
/// arity a+b-2), or `None` if either is unary (join arity would be < 1).
fn tupleset_join(a: &TupleSet, b: &TupleSet) -> Option<TupleSet> {
    if a.arity() < 2 && b.arity() < 2 {
        return None;
    }
    let out_arity = a.arity() + b.arity() - 2;
    if out_arity < 1 {
        return None;
    }
    let mut out = TupleSet::empty(out_arity);
    for ta in a.iter() {
        let left = ta.atoms();
        let mid = *left.last()?;
        for tb in b.iter() {
            let right = tb.atoms();
            if right[0] == mid {
                let mut atoms = left[..left.len() - 1].to_vec();
                atoms.extend_from_slice(&right[1..]);
                out.insert(Tuple::new(atoms));
            }
        }
    }
    Some(out)
}

/// The transpose of a binary tuple set (`None` if not arity 2).
fn tupleset_transpose(a: &TupleSet) -> Option<TupleSet> {
    if a.arity() != 2 {
        return None;
    }
    let mut out = TupleSet::empty(2);
    for t in a.iter() {
        let atoms = t.atoms();
        out.insert(Tuple::new(vec![atoms[1], atoms[0]]));
    }
    Some(out)
}

/// The transitive closure of a binary tuple set (a sound upper for `^r`), by
/// fixpoint (`None` if not arity 2). Deterministic (`BTreeSet` throughout).
fn tupleset_closure(a: &TupleSet) -> Option<TupleSet> {
    if a.arity() != 2 {
        return None;
    }
    let mut out = a.clone();
    loop {
        let step = tupleset_join(&out, a)?;
        let mut grew = false;
        for t in step.iter() {
            if out.insert(t.clone()) {
                grew = true;
            }
        }
        if !grew {
            return Some(out);
        }
    }
}

/// The typed defer for a post-colon `disj` bound on a **quantifier / run-pred
/// param** decl (`x: disj e`). The jar rejects this at resolve ("Local variable
/// … cannot be bound to a 'disjoint' expression", jar-probed 2026-07-18); mettle
/// accepts it leniently (mt-027 over-accept class) and defers here rather than
/// synthesizing a fact for a construct the reference forbids (STYLE E5; zero
/// corpus incidence, pinned by `post_colon_disj_quant_decl_defers_typed`). The
/// post-colon `disj` **field** bound (`f: disj e`) is jar-pinned and lowered
/// (mt-040, [`Lowerer::field_bound_disj_fact`]).
fn bound_disj_unpinned(span: Span) -> TranslateError {
    TranslateError::LoweringUnsupported {
        what: "post-colon `disj` declaration bound".to_owned(),
        span,
    }
}

/// Whether `op` is a declaration-bound multiplicity marker.
fn is_mult_marker(op: UnOp) -> bool {
    matches!(
        op,
        UnOp::SetOf | UnOp::SomeOf | UnOp::LoneOf | UnOp::OneOf | UnOp::ExactlyOf
    )
}

/// The multiplicity test a decl-bound marker enforces on `this.f` (none for
/// `set`/`exactly`).
fn mult_of_marker(op: UnOp) -> Option<MultTest> {
    match op {
        UnOp::SomeOf => Some(MultTest::Some),
        UnOp::LoneOf => Some(MultTest::Lone),
        UnOp::OneOf => Some(MultTest::One),
        UnOp::SetOf | UnOp::ExactlyOf => None,
        _ => None,
    }
}

/// The multiplicity test an arrow-column marker enforces (none for `set`).
fn mult_test_of(m: Option<Mult>) -> Option<MultTest> {
    match m {
        Some(Mult::One) => Some(MultTest::One),
        Some(Mult::Lone) => Some(MultTest::Lone),
        Some(Mult::Some) => Some(MultTest::Some),
        Some(Mult::Set) | None => None,
    }
}

/// The most-negative signed value at bitwidth `bw` (`−2^{bw-1}`; `0` at bw 0).
pub(crate) fn int_min(bw: u32) -> i32 {
    if bw == 0 {
        return 0;
    }
    -(1i32 << (bw - 1))
}

/// The most-positive signed value at bitwidth `bw` (`2^{bw-1}−1`; `0` at bw 0).
pub(crate) fn int_max(bw: u32) -> i32 {
    if bw == 0 {
        return 0;
    }
    (1i32 << (bw - 1)) - 1
}

fn int_binop(op: BinOp) -> Option<IntBinOp> {
    Some(match op {
        BinOp::IntAdd => IntBinOp::Add,
        BinOp::IntSub => IntBinOp::Sub,
        BinOp::IntMul => IntBinOp::Mul,
        BinOp::IntDiv => IntBinOp::Div,
        BinOp::IntRem => IntBinOp::Rem,
        BinOp::Shl => IntBinOp::Shl,
        BinOp::Sha => IntBinOp::Sha,
        BinOp::Shr => IntBinOp::Shr,
        _ => return None,
    })
}

fn temporal_un(op: UnOp) -> (TemporalUnOp, &'static str) {
    match op {
        UnOp::Always => (TemporalUnOp::Always, "always"),
        UnOp::Eventually => (TemporalUnOp::Eventually, "eventually"),
        UnOp::After => (TemporalUnOp::After, "after"),
        UnOp::Before => (TemporalUnOp::Before, "before"),
        UnOp::Historically => (TemporalUnOp::Historically, "historically"),
        UnOp::Once => (TemporalUnOp::Once, "once"),
        _ => unreachable!("non-temporal unary op"),
    }
}

fn temporal_bin(op: BinOp) -> (TemporalBinOp, &'static str) {
    match op {
        BinOp::Until => (TemporalBinOp::Until, "until"),
        BinOp::Releases => (TemporalBinOp::Releases, "releases"),
        BinOp::Since => (TemporalBinOp::Since, "since"),
        BinOp::Triggered => (TemporalBinOp::Triggered, "triggered"),
        _ => unreachable!("non-temporal binary op"),
    }
}

/// Unwraps a defined-field bound `= e` (`ExactlyOf(e)`) to `e`.
fn unwrap_exactly(ast: &Ast, bound: ExprId) -> Option<ExprId> {
    match &ast.exprs[bound].kind {
        ExprKind::Unary {
            op: UnOp::ExactlyOf,
            expr,
        } => Some(*expr),
        _ => None,
    }
}

/// A synthetic span for internal errors that predate any source construct.
fn als_types_synthetic_span() -> Span {
    Span::new(als_syntax::FileId::from_index(0), 0, 0)
}
