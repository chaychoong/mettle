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
//! [`ExprKind::Name`], so there is nothing to descend into.
//!
//! Not called from any dispatch path at mt-065 — mt-067 places it.

use als_syntax::ast::{Ast, BinOp, ExprId, ExprKind, UnOp};

use crate::graph::{ModuleGraph, ModuleId};
use crate::world::{CmdTargetResolved, ResolvedCommand, ResolvedWorld};

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
fn command_formula_has_temporal(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    command: &ResolvedCommand,
) -> bool {
    let facts = world
        .facts
        .iter()
        .any(|fact| module_expr_has_temporal(graph, fact.module, fact.body));
    facts || command_body_has_temporal(world, graph, command)
}

/// The command's own body, per target kind (`CompModule.java:1975-2014`).
fn command_body_has_temporal(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    command: &ResolvedCommand,
) -> bool {
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
            module_expr_has_temporal(graph, func.module, func.body)
        }),
        // `e = assertBody.not()` / the inline block — negation and block
        // wrapping do not change which operators occur.
        CmdTargetResolved::Assert { body, module } | CmdTargetResolved::Block { body, module } => {
            module_expr_has_temporal(graph, *module, *body)
        }
        // Resolution already rejected the model; there is no formula to scan.
        CmdTargetResolved::Unresolved => false,
    }
}

/// Whether the expression tree rooted at `root` (in `module`'s file) contains a
/// temporal operator.
fn module_expr_has_temporal(graph: &ModuleGraph, module: ModuleId, root: ExprId) -> bool {
    let file = graph.modules[module].file;
    expr_has_temporal(graph.files.file(file).ast_ref(), root)
}

/// `Expr.hasTemporal()` over mettle's surface AST: an explicit worklist walk
/// (no recursion — a deeply-nested user expression must not blow the stack)
/// that short-circuits on the first temporal operator.
fn expr_has_temporal(ast: &Ast, root: ExprId) -> bool {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
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
                stack.push(*expr);
            }
            ExprKind::Binary { op, lhs, rhs } => {
                if bin_op_is_temporal(*op) {
                    return true;
                }
                stack.push(*lhs);
                stack.push(*rhs);
            }
            ExprKind::Arrow { lhs, rhs, .. } | ExprKind::Compare { lhs, rhs, .. } => {
                stack.push(*lhs);
                stack.push(*rhs);
            }
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                stack.push(*cond);
                stack.push(*then_branch);
                stack.push(*else_branch);
            }
            // A call's callee is a bare `Name` in the surface AST, so pushing
            // the target cannot descend into a pred body — it only covers the
            // genuine relational box join (`r'[x]`), where the jar's resolved
            // tree is an ordinary binary node whose children it visits too.
            ExprKind::BoxJoin { target, args } => {
                stack.push(*target);
                stack.extend(args.iter().copied());
            }
            ExprKind::Quant { decls, body, .. } | ExprKind::Comprehension { decls, body } => {
                stack.extend(decls.iter().map(|&d| ast.decls[d].bound));
                stack.push(*body);
            }
            ExprKind::Let { bindings, body } => {
                stack.extend(bindings.iter().map(|b| b.value));
                stack.push(*body);
            }
            ExprKind::Block(parts) => stack.extend(parts.iter().copied()),
        }
    }
    false
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
