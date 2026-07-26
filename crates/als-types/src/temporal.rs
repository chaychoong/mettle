//! The temporal/static command discriminator (ADR-0015 decision 1, mt-065).
//!
//! [`is_temporal_model`] answers the one question Rung 6's dispatch turns on:
//! **is this command temporal?** The rule is string-pinned to the reference
//! jar's `CompUtil.isTemporalModel(Iterable<Sig>, Command)`
//! (`docs/reference/alloy6-temporal.md` §(a), `CompUtil.java:189-201`):
//!
//! > a command is temporal iff a `var` sig/field exists in the reachable world,
//! > **or** a temporal operator appears anywhere in the command's
//! > facts-plus-body — either condition alone suffices.
//!
//! Both halves have a *different* reachability scope, and getting them mixed up
//! is the trap this module exists to avoid:
//!
//! - The **`var` half is whole-world.** The jar's `sigs` argument is the
//!   caller's complete reachable-sig list (`TranslateAlloyToKodkod.java:153`
//!   takes it as "must be a complete list"), independent of the command. So a
//!   `var` sig in an *opened module* makes **every** command in the model
//!   temporal, even one whose body never mentions it. [`ResolvedWorld::sigs`]
//!   and `fields` are exactly that whole-world set.
//! - The **operator half is per-command**: `cmd.formula` is
//!   `globalFacts.and(commandBody)` (`CompModule.java:2030`), where
//!   `globalFacts` is every free `fact` body of every reachable module
//!   (`CompModule.getAllReachableFacts`, `:1905-1913` — free facts *only*: a
//!   sig's appended fact goes to `Sig.addFact`, `:1884`, and never enters the
//!   list) and `commandBody` is the target's own formula (`:1975-2014`: a
//!   `check`'s negated assertion, or the named pred/fun's **body**, or the
//!   inline block).
//!
//! The scan itself is `Expr.hasTemporal()`: a full-tree query that
//! short-circuits on any of the 11 temporal operators and **does not descend
//! into a called pred/fun's body** — `VisitQuery.visit(ExprCall)` iterates the
//! call's `args` only (jar bytecode, `edu/mit/csail/sdg/ast/VisitQuery.class`;
//! the query's op set is `Expr$2`'s two `visit` overrides, matching exactly
//! `AFTER`/`BEFORE`/`PRIME`/`HISTORICALLY`/`ALWAYS`/`ONCE`/`EVENTUALLY` and
//! `UNTIL`/`SINCE`/`TRIGGERED`/`RELEASES`). Walking mettle's **surface** AST
//! reproduces that scope for free: a call site is a [`ExprKind::BoxJoin`] over a
//! [`ExprKind::Name`], so there is nothing to descend into — jar-confirmed by
//! probe K1.
//!
//! **A top-level `let` macro is the one exception, and it is not symmetric with
//! a call.** Macro expansion is *textual and pre-resolution* in the jar, so by
//! the time `isTemporalModel` scans `cmd.formula` the macro's body is already
//! spliced in: a macro whose body holds a temporal operator makes the command
//! temporal, whether it is used from a free fact or straight from the command
//! body (probes **K4a**/**K4b**, alloy6-temporal.md §(m); this refuted mt-065's
//! original surface-only walk, which saw the use as an opaque
//! [`ExprKind::Name`]). The walk therefore follows macro *definitions* while
//! still refusing to follow func/pred *calls*. It gets the macro identity from
//! the same seam the lowerer replays expansions through — the recorded
//! [`crate::choice::MacroChoice`] — never by re-deriving name resolution.
//!
//! Not called from any dispatch path at mt-065 — mt-067 places it.

use std::collections::BTreeSet;

use als_syntax::ast::{Ast, BinOp, ExprId, ExprKind, UnOp};

use crate::choice::{ChoiceTable, ExprChoice, MacroChoice, NameChoice, SpineChoice};
use crate::graph::{ModuleGraph, ModuleId};
use crate::world::{CmdTargetResolved, MacroId, ResolvedCommand, ResolvedWorld};

/// Whether `command` is a **temporal** command — the pinned discriminator
/// (alloy6-temporal.md §(a)).
///
/// `true` means Rung 6's bounded-lasso path owns the command and a `steps`
/// scope is legal on it; `false` means the ordinary static pipeline owns it and
/// a `steps` scope is a reject ("You cannot set a scope on \"steps\" in static
/// models.", probe T-03).
#[must_use]
pub fn is_temporal_model(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    command: &ResolvedCommand,
) -> bool {
    world_has_var(world) || command_formula_has_temporal(world, graph, command)
}

/// The `var`-declaration half: any non-builtin `var` sig, or any `var` field,
/// anywhere in the reachable world (`CompUtil.java:190-197`).
///
/// The jar's loop reads `if (sig.isVariable != null && !sig.builtin) return
/// true; else { for each field decl: if (dec.isVar != null) return true; }` —
/// the `else` only skips the field scan of a sig that already returned, and a
/// builtin sig declares no fields, so the disjunction below is equivalent.
fn world_has_var(world: &ResolvedWorld) -> bool {
    world
        .sigs
        .iter()
        .any(|(_, sig)| sig.is_var && !sig.is_builtin)
        || world.fields.iter().any(|(_, field)| field.is_var)
}

/// The operator half: does a temporal operator appear in `globalFacts and
/// commandBody` (`CompModule.java:2030`)?
///
/// One [`Scan`] serves the whole command, so a macro used by several facts (or
/// by a fact *and* the body) has its body examined once.
fn command_formula_has_temporal(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    command: &ResolvedCommand,
) -> bool {
    let mut scan = Scan {
        world,
        graph,
        expanded: BTreeSet::new(),
    };
    let facts = world
        .facts
        .iter()
        .any(|fact| scan.run(fact.module, fact.body, &world.choices));
    facts || command_body_has_temporal(&mut scan, command)
}

/// The command's own body, per target kind (`CompModule.java:1975-2014`).
fn command_body_has_temporal(scan: &mut Scan<'_>, command: &ResolvedCommand) -> bool {
    let world = scan.world;
    match &command.target {
        // `e = f.getBody()` — the pred/fun body is substituted **directly**
        // into the command formula, so a temporal operator written inside the
        // run/checked predicate does count (unlike one inside a pred that body
        // merely *calls*). A `fun` target additionally conjoins `body in
        // returnDecl` and a parametric target wraps `some decls |`, but `Func`'s
        // constructor already rejects temporal operators in both a return
        // declaration and a parameter declaration (`Func.java:201-207`), so the
        // body alone decides. mettle records the matching overloads; the jar
        // errors on more than one, so this is a singleton in practice.
        CmdTargetResolved::Named(funcs) => funcs.iter().any(|&f| {
            let func = &world.funcs[f];
            scan.run(func.module, func.body, &world.choices)
        }),
        // `e = assertBody.not()` / the inline block — negation and block
        // wrapping do not change which operators occur.
        CmdTargetResolved::Assert { body, module } | CmdTargetResolved::Block { body, module } => {
            scan.run(*module, *body, &world.choices)
        }
        // Resolution already rejected the model; there is no formula to scan.
        CmdTargetResolved::Unresolved => false,
    }
}

/// One command's `Expr.hasTemporal()` scan: the walk plus the set of macro
/// bodies it has already examined.
struct Scan<'a> {
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    /// Macros whose body this scan has already walked. Dual-purpose (STYLE
    /// C2/D2 — `BTreeSet` so nothing hash-ordered can leak, though only
    /// membership is read):
    ///
    /// 1. **Work bound.** Re-walking a macro body cannot reveal a new operator
    ///    — the body AST is the same tree at every use site, and a use site's
    ///    *arguments* are walked separately, in the calling module. So each
    ///    body is walked at most once even if used a hundred times, keeping the
    ///    scan linear in the model rather than exponential in macro nesting.
    /// 2. **Cycle guard.** Alloy forbids recursive macros (resolution-doc
    ///    §3.7), but the walk does not trust that: a cycle would simply hit an
    ///    already-expanded id and stop. [`Scan::run`] asserts the resulting
    ///    negative space (no more expansions than the world has macros).
    expanded: BTreeSet<MacroId>,
}

/// One worklist entry: an expression, the module whose AST holds it, and the
/// choice table its names resolved under (a macro body's names resolve under
/// the *nested* table captured at its use site, not the world's top table).
type Frame<'a> = (ModuleId, ExprId, &'a ChoiceTable);

impl<'a> Scan<'a> {
    /// `Expr.hasTemporal()` over mettle's surface AST: an explicit worklist walk
    /// (no recursion — a deeply-nested user expression must not blow the stack)
    /// that short-circuits on the first temporal operator, and splices in the
    /// body of any macro it meets (probes K4a/K4b).
    fn run(&mut self, module: ModuleId, root: ExprId, choices: &'a ChoiceTable) -> bool {
        let world = self.world;
        let mut stack: Vec<Frame<'a>> = vec![(module, root, choices)];
        while let Some((module, id, choices)) = stack.pop() {
            // A macro use is *not* a call: the jar splices the body in before
            // `isTemporalModel` runs, so its operators are visible (K4a/K4b).
            // The `MacroChoice` is the lowerer's own replay seam
            // (`als_core::lower::replay_macro_*`), so name resolution is read,
            // never re-derived (resolution-doc §4.4).
            if let Some(mc) = macro_use(choices, module, id) {
                if self.expanded.insert(mc.macro_id) {
                    stack.push((
                        mc.body_module,
                        world.macros[mc.macro_id].body,
                        &mc.body_choices,
                    ));
                }
            }
            let ast = self.ast_of(module);
            // Children stay in the frame they were written in: only a macro
            // expansion changes `(module, choices)`.
            let mut push = |child: ExprId| stack.push((module, child, choices));
            match &ast.exprs[id].kind {
                // Leaves: nothing to descend into.
                ExprKind::Num(_)
                | ExprKind::Str(_)
                | ExprKind::Const(_)
                | ExprKind::This
                | ExprKind::Name(_)
                | ExprKind::AtName(_) => {}
                ExprKind::Unary { op, expr } => {
                    if un_op_is_temporal(*op) {
                        return true;
                    }
                    push(*expr);
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    if bin_op_is_temporal(*op) {
                        return true;
                    }
                    push(*lhs);
                    push(*rhs);
                }
                ExprKind::Arrow { lhs, rhs, .. } | ExprKind::Compare { lhs, rhs, .. } => {
                    push(*lhs);
                    push(*rhs);
                }
                ExprKind::IfThenElse {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    push(*cond);
                    push(*then_branch);
                    push(*else_branch);
                }
                // A call's callee is a bare `Name` in the surface AST, so
                // pushing the target cannot descend into a pred body — it only
                // covers the genuine relational box join (`r'[x]`), where the
                // jar's resolved tree is an ordinary binary node whose children
                // it visits too. A *macro* application is the same shape, and
                // its body was already spliced in above; pushing the args here
                // is what covers a temporal operator passed as an argument.
                ExprKind::BoxJoin { target, args } => {
                    push(*target);
                    args.iter().copied().for_each(&mut push);
                }
                ExprKind::Quant { decls, body, .. } | ExprKind::Comprehension { decls, body } => {
                    decls
                        .iter()
                        .map(|&d| ast.decls[d].bound)
                        .for_each(&mut push);
                    push(*body);
                }
                ExprKind::Let { bindings, body } => {
                    bindings.iter().map(|b| b.value).for_each(&mut push);
                    push(*body);
                }
                ExprKind::Block(parts) => parts.iter().copied().for_each(&mut push),
            }
        }
        // Negative space (STYLE I1/I3): the expansion set is a strict subset of
        // the world's macros, so no cycle — and no unbounded expansion — is
        // possible even though Alloy's own no-recursive-macro rule is not
        // trusted here.
        debug_assert!(
            self.expanded.len() <= world.macros.len(),
            "macro expansion exceeded the world's macro count: {} > {}",
            self.expanded.len(),
            world.macros.len()
        );
        false
    }

    /// The parsed AST holding `module`'s expressions.
    fn ast_of(&self, module: ModuleId) -> &'a Ast {
        let file = self.graph.modules[module].file;
        self.graph.files.file(file).ast_ref()
    }
}

/// The macro `(module, expr)` resolved to, if it resolved to one — a 0-param
/// macro used as a value ([`NameChoice::Macro`]) or a macro application
/// ([`SpineChoice::Macro`]). Every other choice (including a func/pred call,
/// deliberately) yields `None`.
fn macro_use(choices: &ChoiceTable, module: ModuleId, expr: ExprId) -> Option<&MacroChoice> {
    match choices.get(module, expr)? {
        ExprChoice::Name(NameChoice::Macro(mc)) | ExprChoice::Spine(SpineChoice::Macro(mc)) => {
            Some(mc)
        }
        ExprChoice::Name(_) | ExprChoice::Spine(_) => None,
    }
}

/// The seven unary members of the pinned 11-operator set (`ExprUnary$Op`:
/// `AFTER`, `BEFORE`, `PRIME`, `HISTORICALLY`, `ALWAYS`, `ONCE`, `EVENTUALLY`).
fn un_op_is_temporal(op: UnOp) -> bool {
    match op {
        UnOp::Always
        | UnOp::Eventually
        | UnOp::After
        | UnOp::Before
        | UnOp::Historically
        | UnOp::Once
        | UnOp::Prime => true,
        UnOp::Not
        | UnOp::No
        | UnOp::Some
        | UnOp::Lone
        | UnOp::One
        | UnOp::SetOf
        | UnOp::SomeOf
        | UnOp::LoneOf
        | UnOp::OneOf
        | UnOp::SeqOf
        | UnOp::Transpose
        | UnOp::Closure
        | UnOp::ReflexiveClosure
        | UnOp::ExactlyOf
        | UnOp::Card
        | UnOp::IntOf
        | UnOp::SumOf => false,
    }
}

/// The four binary members of the pinned set (`ExprBinary$Op`: `UNTIL`,
/// `SINCE`, `TRIGGERED`, `RELEASES`), plus `;`.
///
/// **Assumption (mt-069-verifiable):** `;` counts. It is not a member of
/// `ExprBinary$Op` at all — the jar's parser desugars `a ; b` into `a and after
/// b` before resolution (mettle does the same at lowering,
/// `als_core::lower`), so the tree `hasTemporal()` actually scans contains an
/// `AFTER`. Treating the surface `;` as temporal-bearing reproduces that; a
/// probe on `sig A {} fact { some A ; some A } run {}` would confirm it
/// directly.
fn bin_op_is_temporal(op: BinOp) -> bool {
    match op {
        BinOp::Until | BinOp::Releases | BinOp::Since | BinOp::Triggered | BinOp::Seq => true,
        BinOp::Or
        | BinOp::And
        | BinOp::Iff
        | BinOp::Implies
        | BinOp::Join
        | BinOp::Union
        | BinOp::Diff
        | BinOp::Intersect
        | BinOp::Override
        | BinOp::DomRestrict
        | BinOp::RanRestrict
        | BinOp::Shl
        | BinOp::Sha
        | BinOp::Shr
        | BinOp::IntAdd
        | BinOp::IntSub
        | BinOp::IntMul
        | BinOp::IntDiv
        | BinOp::IntRem => false,
    }
}
