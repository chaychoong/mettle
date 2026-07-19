//! Referenced-string-literal collection (mt-045, translation-ref §13,
//! LEDGER-007) — the port of the jar's `Command.getAllStringConstants(sigs)`.
//!
//! The `String` sig's atoms are exactly the string literals the command can
//! *reach*, padded (when a `for … but N String` scope is given) to `N`. This
//! module owns the *reach* half: walking the resolved AST to gather every
//! `ExprKind::Str` the command's goal touches, so [`crate::scope`] can mint the
//! matching atoms. The rule (translation-ref §13, probes S6/S7):
//!
//! - the command's **goal formula** (its target pred/assert/block body);
//! - **every** reachable module's free **facts**;
//! - **every** reachable sig's **appended fact** and every field's
//!   **declaration bound** expression;
//! - **recursing into the bodies of *called* funcs/preds only** — a literal
//!   reachable exclusively through an *uncalled* pred is **not** collected
//!   (probe S7). "Called" is read from the same [`als_types::choice`] table the
//!   lowerer inlines from, so the two can never drift.
//!
//! The result is the set of literal *contents* (the `ExprKind::Str` payload,
//! already unescaped, quote characters stripped by the lexer). [`crate::scope`]
//! forms the universe atom by re-adding the surrounding quotes (the atom for
//! literal `"hi"` is the 4-char string `"hi"`, translation-ref §13.1).
//!
//! **Determinism.** The jar collects into a `HashSet` (order nondeterministic —
//! probe S2 shows `"String1"` before `"String0"`); mettle collects into a
//! [`BTreeSet`], so the atom order among literals is the deterministic
//! lexicographic order of their contents. String atoms are symmetric, so
//! verdict and SB-0 count are provably order-independent (LEDGER-007).

use std::collections::BTreeSet;

use als_syntax::ast::{Ast, ExprId, ExprKind};
use als_types::choice::{ChoiceTable, ExprChoice, MacroChoice, NameChoice, SpineChoice};
use als_types::{CmdTargetResolved, FuncId, ModuleGraph, ModuleId, ResolvedCommand, ResolvedWorld};

/// Collects every string literal the `command`'s goal can reach
/// (translation-ref §13, LEDGER-007). Returns the literal *contents* (no
/// surrounding quotes), deterministically ordered.
pub(crate) fn collect_referenced_literals(
    world: &ResolvedWorld,
    graph: &ModuleGraph,
    command: &ResolvedCommand,
) -> BTreeSet<String> {
    let mut c = Collector {
        world,
        graph,
        literals: BTreeSet::new(),
        visited_funcs: BTreeSet::new(),
    };
    let top = &world.choices;

    // 1. The command's goal formula — its target pred/assert/block body. A `run
    //    p` names the pred whose body *is* the goal (so it counts as "called");
    //    an inline block/assert is walked directly. The lowerer inlines only the
    //    first overload (`funcs.first()`, deferring on >1), so collection matches
    //    it — a >1 command never solves, making any divergence moot regardless.
    match &command.target {
        CmdTargetResolved::Named(funcs) => {
            if let Some(&f) = funcs.first() {
                c.walk_func(f);
            }
        }
        CmdTargetResolved::Assert { body, module } | CmdTargetResolved::Block { body, module } => {
            c.walk(*module, top, *body);
        }
        CmdTargetResolved::Unresolved => {}
    }

    // 2. Every reachable module fact (translation-ref §2.5(2), probe S6).
    for fact in &world.facts {
        c.walk(fact.module, top, fact.body);
    }

    // 3. Every reachable sig's appended fact and every field's declaration
    //    bound expression (translation-ref §13).
    for (_, sig) in world.sigs.iter() {
        if let Some(body) = sig.appended_fact {
            c.walk(sig.module, top, body);
        }
    }
    for (_, field) in world.fields.iter() {
        let module = world.sigs[field.owner].module;
        c.walk(module, top, field.bound);
    }

    c.literals
}

/// The collection walk state. `visited_funcs` is both the recursion guard (the
/// reference rejects recursive funcs; here it just prevents re-walking) and a
/// dedup so a func called from many sites is walked once.
struct Collector<'a> {
    world: &'a ResolvedWorld,
    graph: &'a ModuleGraph,
    literals: BTreeSet<String>,
    visited_funcs: BTreeSet<FuncId>,
}

impl<'a> Collector<'a> {
    fn ast(&self, module: ModuleId) -> &'a Ast {
        let file = self.graph.modules[module].file;
        self.graph.files.file(file).ast_ref()
    }

    /// Walks a called func/pred body once (guarded), under the world's top
    /// choice table (funcs resolve at module scope).
    fn walk_func(&mut self, func: FuncId) {
        if !self.visited_funcs.insert(func) {
            return;
        }
        let f = &self.world.funcs[func];
        let (module, body, return_decl) = (f.module, f.body, f.return_decl);
        let top = &self.world.choices;
        // A `fun`'s return declaration can carry a literal bound too; walk it.
        if let Some(decl) = return_decl {
            self.walk(module, top, decl);
        }
        self.walk(module, top, body);
    }

    /// Walks expression `e` (in `module`, resolved under `choices`), collecting
    /// `Str` literals and recursing into called funcs/preds and expanded macros.
    fn walk(&mut self, module: ModuleId, choices: &ChoiceTable, e: ExprId) {
        // Follow any call/macro resolution first — these reach bodies the
        // structural children never mention.
        self.follow_choice(module, choices, e);

        let node = &self.ast(module).exprs[e];
        match &node.kind {
            ExprKind::Str(s) => {
                self.literals.insert(s.clone());
            }
            ExprKind::Num(_)
            | ExprKind::Const(_)
            | ExprKind::This
            | ExprKind::Name(_)
            | ExprKind::AtName(_) => {}
            ExprKind::Unary { expr, .. } => self.walk(module, choices, *expr),
            ExprKind::Binary { lhs, rhs, .. }
            | ExprKind::Compare { lhs, rhs, .. }
            | ExprKind::Arrow { lhs, rhs, .. } => {
                self.walk(module, choices, *lhs);
                self.walk(module, choices, *rhs);
            }
            ExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.walk(module, choices, *cond);
                self.walk(module, choices, *then_branch);
                self.walk(module, choices, *else_branch);
            }
            ExprKind::BoxJoin { target, args } => {
                self.walk(module, choices, *target);
                for &a in args {
                    self.walk(module, choices, a);
                }
            }
            ExprKind::Quant { decls, body, .. } | ExprKind::Comprehension { decls, body } => {
                let ast = self.ast(module);
                for &d in decls {
                    self.walk(module, choices, ast.decls[d].bound);
                }
                self.walk(module, choices, *body);
            }
            ExprKind::Let { bindings, body } => {
                for b in bindings {
                    self.walk(module, choices, b.value);
                }
                self.walk(module, choices, *body);
            }
            ExprKind::Block(exprs) => {
                for &b in exprs {
                    self.walk(module, choices, b);
                }
            }
        }
    }

    /// If `(module, e)` resolved to a func/pred call or a macro expansion,
    /// recurse into the callee body (translation-ref §13: recurse into *called*
    /// funcs only). Macros are replayed under their nested choice table, exactly
    /// as the lowerer expands them.
    fn follow_choice(&mut self, module: ModuleId, choices: &ChoiceTable, e: ExprId) {
        match choices.get(module, e) {
            Some(ExprChoice::Spine(SpineChoice::Call(cc))) => {
                let func = cc.func;
                self.walk_func(func);
            }
            Some(ExprChoice::Name(NameChoice::Call0(func))) => {
                let func = *func;
                self.walk_func(func);
            }
            Some(
                ExprChoice::Spine(SpineChoice::Macro(mc)) | ExprChoice::Name(NameChoice::Macro(mc)),
            ) => {
                // Clone the record out so the walk can borrow `self` mutably (the
                // nested table + args are owned by `choices`, not `self`).
                let mc = mc.clone();
                self.walk_macro(module, choices, &mc);
            }
            _ => {}
        }
    }

    /// Walks an expanded macro body under its own nested choice table, plus the
    /// call-site arguments under the caller's table (mirrors the lowerer's macro
    /// replay — the args live in `arg_module`, the body in `body_module`).
    fn walk_macro(&mut self, arg_module: ModuleId, arg_choices: &ChoiceTable, mc: &MacroChoice) {
        for &a in &mc.args {
            self.walk(arg_module, arg_choices, a);
        }
        let body = self.world.macros[mc.macro_id].body;
        self.walk(mc.body_module, &mc.body_choices, body);
    }
}
