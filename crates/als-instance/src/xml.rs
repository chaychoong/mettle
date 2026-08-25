//! The **instance-XML writer** (mt-071): a jar-shape-exact reimplementation of
//! `A4Solution.writeXML` / `A4SolutionWriter.writeInstance`.
//!
//! Implemented straight from `docs/reference/alloy6-instance-xml.md` (probe
//! wave X-01..X-09b) — that document *is* this module's specification, and
//! every non-obvious branch below cites the section it comes from. Semantics
//! faithful, structure idiomatic (`PORTING_RULES` prime directive): the
//! reference's recursive `writeSig`/`writeField`/`writeSkolem` shape is
//! reproduced as an ordinary Rust walk over mettle's own arenas — no
//! `IdentityHashMap`, no `Expr` object identity, no `Rc<RefCell>`.
//!
//! The four pins that shape everything here:
//!
//! 1. **IDs are lazy touch-order** (§2). The reference's `map(Expr)` hands out
//!    `map.size()` the first time *any* print statement mentions a sig / field
//!    / skolem — which routinely happens while building a *different* sig's
//!    `parentID=`. [`Ids`] is that map, keyed by [`XmlKey`] rather than by
//!    object identity, and it is rebuilt per `<instance>` block exactly as the
//!    reference's per-state constructor rebuilds its own.
//! 2. **Fields interleave** immediately after their owning `</sig>` (§2),
//!    mid-recursion — never batched.
//! 3. **The `macros` mechanism is the live path** (§§6-7): the real GUI/CLI
//!    caller always passes every reachable user `fun`/`pred`, so every zero-arg
//!    relational `fun` mints an `m<i>`-namespaced `<skolem>`, and a reachable
//!    such `fun` with nonzero past-depth makes the physical block count
//!    `tracelength + extra·(tracelength − loopState)`, **not** `tracelength`.
//! 4. **Determinism** (§12): no hash iteration anywhere near ID assignment or
//!    emission order — `BTreeMap`/`Vec` only, every walk driven by arena order.
//!
//! Deliberately out of scope: `writeMetamodel` (§10), a separate entry point
//! that never co-occurs with a solved instance.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use als_core::bounds::{AtomId, Tuple, TupleSet, Universe};
use als_core::ir::{Ir, RelId};
use als_core::{
    eliminate_fragment_at_state, lower_fragment, lower_fragment_keeping_temporal, normalize_state,
    BoundsResult, Evaluator, FragmentInput, FragmentRoot, Instance, LoweredFragment, LoweredGoal,
    ScopedUniverse, SolveOptions, TemporalTrace, TranslateError,
};
use als_syntax::ast::{
    Ast, BinOp, CmdKind, DeclId, Expect, ExprId, ExprKind, Para, ParaName, SigMult, UnOp,
};
use als_syntax::ArenaId as _;
use als_types::{
    CmdTargetResolved, FieldId, FuncId, ModuleGraph, ModuleId, ResolvedWorld, SigId, SigKind,
    StepsMax, Type,
};

/// The `builddate=` value mettle writes (§1). The reference writes its jar's
/// own fixed build-time string; mettle has no such stamp and must not read a
/// clock (determinism, §12), so it writes its own version constant. Nothing
/// consumes the attribute — `A4SolutionReader` never even looks for it
/// (bytecode-checked, mt-071).
const BUILDDATE: &str = concat!("mettle ", env!("CARGO_PKG_VERSION"));

/// What a solved command hands the writer: the artifacts one `<alloy>` document
/// is rendered from.
///
/// Every field is a borrow of something the solve pipeline already produced —
/// index/ID-based throughout, owning no graph structure (arena discipline).
#[derive(Debug)]
pub struct XmlRequest<'a> {
    /// The resolved world the command was solved against.
    pub world: &'a ResolvedWorld,
    /// The module graph — module labels, assert names, and `<source>` text.
    pub graph: &'a ModuleGraph,
    /// The command's scope-phase output (universe, bitwidth, `maxseq`).
    pub scoped: &'a ScopedUniverse,
    /// The bounds-phase output: the sig/field denotation seam every printed
    /// value is evaluated through.
    pub bounds: &'a BoundsResult,
    /// Index into [`ResolvedWorld::commands`] of the solved command.
    pub command: usize,
    /// The `filename=` attribute (§1) — a plain string the *caller* owns. The
    /// reference's evaluator reparse breaks on an empty one, so callers pass
    /// the model path they were given.
    pub filename: &'a str,
    /// The options the solve actually used (after any `expect 1` override).
    pub opts: SolveOptions,
    /// The solved artifacts themselves.
    pub solution: XmlSolution<'a>,
}

/// The two shapes a solved command comes in.
#[derive(Copy, Clone, Debug)]
pub enum XmlSolution<'a> {
    /// A static command: one state (before any macro-driven unrolling, §7).
    Static {
        /// The decoded instance.
        instance: &'a Instance,
        /// The lowered goal, for its skolem relations (§6).
        goal: &'a LoweredGoal,
    },
    /// A temporal command: the solved lasso.
    Trace {
        /// The trace, whose states, loop target and artifacts drive both the
        /// per-block values and the block count.
        trace: &'a TemporalTrace,
    },
}

/// Renders the whole `<alloy>` document for one solved command.
///
/// `ir` is taken mutably because the **macro** mechanism (§6) evaluates every
/// reachable zero-arg `fun`'s body, which lowers fresh nodes into the same
/// arena the solve used — append-only, so nothing already solved is disturbed
/// (the contract [`lower_fragment`] already gives the REPL).
///
/// # Errors
/// A [`TranslateError`] when a macro body cannot be lowered or evaluated
/// against the solved instance. A macro the reference would have written is
/// never silently dropped (STYLE E5).
pub fn write_instance_xml(ir: &mut Ir, req: &XmlRequest<'_>) -> Result<String, TranslateError> {
    let plan = Plan::build(ir, req);
    let macros = lower_macros(ir, req, &plan)?;
    let blocks = evaluate_blocks(ir, req, &plan, &macros)?;

    let mut out = String::new();
    out.push_str("<alloy builddate=\"");
    escape_into(&mut out, BUILDDATE);
    out.push_str("\">\n\n");
    let universe = Plan::universe_of(req);
    for values in &blocks {
        BlockWriter {
            world: req.world,
            plan: &plan,
            values,
            universe,
            ids: Ids::default(),
            out: &mut out,
        }
        .write_block(req);
    }
    // `<source>` entries come once per loaded file, after **every**
    // `<instance>` block, immediately before `</alloy>` (§9).
    for (_, file) in req.graph.files.iter() {
        out.push_str("\n<source filename=\"");
        escape_into(&mut out, &file.path);
        out.push_str("\" content=\"");
        escape_into(&mut out, &file.source);
        out.push_str("\"/>\n");
    }
    out.push_str("\n</alloy>\n");
    Ok(out)
}

// ----------------------------------------------------------------- the plan

/// One reachable zero-arg relational `fun` — a **macro** in the reference's
/// sense (§6): the writer synthesizes an `m<i>`-namespaced `<skolem>` for it in
/// every `<instance>` block.
#[derive(Clone, Debug)]
struct MacroDef {
    func: FuncId,
    /// `"$" + label-with-every-leading-`$`-stripped` (§6).
    label: String,
    private: bool,
}

/// One ordinary skolem, resolved once: the relation, its minted name, and the
/// column sigs its `<types>` reports.
#[derive(Clone, Debug)]
struct SkolemDef {
    rel: RelId,
    name: String,
    types: Vec<SigId>,
}

/// The structural decisions taken once, before any block renders: which sigs
/// are written in which order, how many blocks there are, and the header text.
#[derive(Debug)]
struct Plan {
    /// `children(UNIV)` — the reference's `toplevels` list (§2): the `sigs`
    /// argument filtered to prim sigs whose parent is `univ`. `none` is absent
    /// (its jar counterpart has a null parent, so it never lands here).
    toplevels: Vec<SigId>,
    /// Prim children of each prim sig, in declaration order.
    children: BTreeMap<SigId, Vec<SigId>>,
    /// Subset sigs, written top-level after the whole `univ` tree (§3).
    subsets: Vec<SigId>,
    /// The command's ordinary skolems, in mint order (§6).
    skolems: Vec<SkolemDef>,
    /// The macros (§6) in `FuncId` order — the `m<i>` numbering follows it.
    macros: Vec<MacroDef>,
    /// Trace length (1 for a static command).
    tracelength: usize,
    /// Back-loop target (0 for a static command).
    loop_state: usize,
    /// Physical `<instance>` block count: `tracelength + extra·(tracelength −
    /// loopState)` (§7).
    blocks: usize,
    /// `mintrace=` — `-1` sentinel for a static command (§1).
    mintrace: i64,
    /// `maxtrace=` — same sentinel.
    maxtrace: i64,
    /// The `command=` attribute: the reference's `Command.toString()` (§1).
    command_text: String,
}

impl Plan {
    fn build(ir: &Ir, req: &XmlRequest<'_>) -> Self {
        let world = req.world;
        let univ = world.builtins.univ;
        let none = world.builtins.none;

        let mut toplevels = Vec::new();
        let mut children: BTreeMap<SigId, Vec<SigId>> = BTreeMap::new();
        let mut subsets = Vec::new();
        for (id, sig) in world.sigs.iter() {
            match &sig.kind {
                SigKind::Prim { parent } => match parent {
                    _ if id == none => {}
                    Some(p) if *p == univ => toplevels.push(id),
                    Some(p) => children.entry(*p).or_default().push(id),
                    None => {}
                },
                SigKind::Subset { .. } => subsets.push(id),
            }
        }

        let goal = solution_goal(req);
        let universe = Self::universe_of(req);
        let skolems = goal
            .skolem_bounds
            .iter()
            .map(|(rel, bound)| SkolemDef {
                rel: *rel,
                name: ir.relations[*rel].name.clone(),
                types: bound_types(world, universe, bound.upper()),
            })
            .collect();
        let (tracelength, loop_state) = match req.solution {
            XmlSolution::Static { .. } => (1, 0),
            XmlSolution::Trace { trace } => (trace.states.len(), trace.loop_state),
        };

        let macros = collect_macros(world, req.graph);
        // `extra = max over eligible macros of body.pastDepth()` (§7). Only a
        // past operator makes this nonzero, so a static command's block count
        // always collapses back to `tracelength`.
        let extra = macros
            .iter()
            .map(|m| macro_past_depth(req, m.func))
            .max()
            .unwrap_or(0);
        let blocks = tracelength + extra * (tracelength - loop_state);

        let (mintrace, maxtrace) = match req.solution {
            XmlSolution::Static { .. } => (-1, -1),
            XmlSolution::Trace { .. } => {
                let range = world.commands[req.command].steps_range();
                let max = match range.max {
                    StepsMax::Bounded(n) => i64::from(n),
                    // Unreachable from a solved trace: an open range is a typed
                    // defer long before any instance exists.
                    StepsMax::Unbounded => -1,
                };
                (i64::from(range.min), max)
            }
        };

        Plan {
            toplevels,
            children,
            subsets,
            skolems,
            macros,
            tracelength,
            loop_state,
            blocks,
            mintrace,
            maxtrace,
            command_text: command_text(world, req.graph, req.command),
        }
    }

    fn universe_of<'a>(req: &XmlRequest<'a>) -> &'a Universe {
        match req.solution {
            XmlSolution::Static { instance, .. } => &instance.universe,
            XmlSolution::Trace { trace } => &trace.artifacts.instance.universe,
        }
    }

    /// `children(sig)` (§2): the `toplevels` list for `univ`, the native subsig
    /// list otherwise.
    fn children_of(&self, sig: SigId, univ: SigId) -> &[SigId] {
        if sig == univ {
            &self.toplevels
        } else {
            self.children.get(&sig).map_or(&[][..], Vec::as_slice)
        }
    }
}

/// The lowered goal behind either solution shape — the two carry it in
/// different places, and only its skolem bounds matter here.
fn solution_goal<'a>(req: &XmlRequest<'a>) -> &'a LoweredGoal {
    match req.solution {
        XmlSolution::Static { goal, .. } => goal,
        XmlSolution::Trace { trace } => &trace.artifacts.goal,
    }
}

/// Every reachable zero-arg **relational** `fun`, in `FuncId` order — the
/// reference's `getAllReachableUserDefinedFunc()` under the writer's own
/// `count()==0 && call().type().hasTuple()` gate (§6).
///
/// `util/integer` is excluded because the reference's reachable-func
/// enumeration excludes it by module name (`CompModule.java:1785`), not because
/// of anything the writer itself does.
fn collect_macros(world: &ResolvedWorld, graph: &ModuleGraph) -> Vec<MacroDef> {
    let mut macros = Vec::new();
    for (id, func) in world.funcs.iter() {
        if !func.params.is_empty() || func.is_pred || !func.return_ty.has_tuple(world) {
            continue;
        }
        if graph.modules[func.module].module_name == ["util", "integer"] {
            continue;
        }
        macros.push(MacroDef {
            func: id,
            label: format!("${}", func.qualified_name.trim_start_matches('$')),
            private: func.is_private,
        });
    }
    macros
}

/// `Func.getBody().pastDepth()` for one macro (§7).
fn macro_past_depth(req: &XmlRequest<'_>, func: FuncId) -> usize {
    let f = &req.world.funcs[func];
    let file = req.graph.modules[f.module].file;
    past_depth(req.graph.files.file(file).ast_ref(), f.body)
}

/// The past-operator nesting depth of one expression: `before`/`historically`/
/// `once` and `since`/`triggered` each add a level; every other node takes the
/// maximum over its children.
fn past_depth(ast: &Ast, expr: ExprId) -> usize {
    let d = |e: ExprId| past_depth(ast, e);
    let decls = |ds: &[DeclId]| {
        ds.iter()
            .map(|&id| past_depth(ast, ast.decls[id].bound))
            .max()
            .unwrap_or(0)
    };
    match &ast.exprs[expr].kind {
        ExprKind::Num(_)
        | ExprKind::Str(_)
        | ExprKind::Const(_)
        | ExprKind::This
        | ExprKind::Name(_)
        | ExprKind::AtName(_) => 0,
        ExprKind::Unary { op, expr } => {
            let past = usize::from(matches!(op, UnOp::Before | UnOp::Historically | UnOp::Once));
            past + d(*expr)
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let past = usize::from(matches!(op, BinOp::Since | BinOp::Triggered));
            past + d(*lhs).max(d(*rhs))
        }
        ExprKind::Arrow { lhs, rhs, .. } | ExprKind::Compare { lhs, rhs, .. } => {
            d(*lhs).max(d(*rhs))
        }
        ExprKind::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => d(*cond).max(d(*then_branch)).max(d(*else_branch)),
        ExprKind::BoxJoin { target, args } => args
            .iter()
            .map(|&a| d(a))
            .max()
            .unwrap_or(0)
            .max(d(*target)),
        ExprKind::Quant {
            decls: ds, body, ..
        }
        | ExprKind::Comprehension { decls: ds, body } => decls(ds).max(d(*body)),
        ExprKind::Let { bindings, body } => bindings
            .iter()
            .map(|b| d(b.value))
            .max()
            .unwrap_or(0)
            .max(d(*body)),
        ExprKind::Block(items) => items.iter().map(|&e| d(e)).max().unwrap_or(0),
    }
}

// -------------------------------------------------------- values per block

/// Everything one `<instance>` block prints, already evaluated — the walk
/// itself is then pure string building.
#[derive(Debug, Default)]
struct BlockValues {
    sigs: BTreeMap<SigId, TupleSet>,
    fields: BTreeMap<FieldId, TupleSet>,
    skolems: BTreeMap<RelId, TupleSet>,
    /// Parallel to [`Plan::macros`].
    macros: Vec<TupleSet>,
}

/// One macro's body, lowered once per block (a temporal body is eliminated at
/// each block's own time index, so the entries genuinely differ).
#[derive(Debug)]
struct LoweredMacro {
    per_block: Vec<LoweredFragment>,
}

/// Lowers every macro body into `ir` — the one phase needing `&mut Ir`, kept
/// separate so the evaluation phase can borrow the arena immutably.
fn lower_macros(
    ir: &mut Ir,
    req: &XmlRequest<'_>,
    plan: &Plan,
) -> Result<Vec<LoweredMacro>, TranslateError> {
    let mut out = Vec::with_capacity(plan.macros.len());
    for m in &plan.macros {
        let func = &req.world.funcs[m.func];
        let file = req.graph.modules[func.module].file;
        let input = FragmentInput {
            module: func.module,
            ast: req.graph.files.file(file).ast_ref(),
            choices: &req.world.choices,
            expr: func.body,
            bitwidth: req.scoped.bitwidth,
            globals: &[],
            root: FragmentRoot::Value,
        };
        let per_block = match req.solution {
            XmlSolution::Static { .. } => {
                let frag = lower_fragment(req.world, req.graph, req.bounds, ir, &input)?;
                vec![frag; plan.blocks]
            }
            XmlSolution::Trace { trace } => {
                // A macro body may itself be temporal — that is exactly what
                // makes `extra > 0` — so it keeps its temporal nodes and is
                // eliminated at each block's own time index, by the same
                // LTL-on-lasso machinery the solve and the REPL use.
                let kept =
                    lower_fragment_keeping_temporal(req.world, req.graph, req.bounds, ir, &input)?;
                (0..plan.blocks)
                    .map(|b| {
                        eliminate_fragment_at_state(
                            ir,
                            &trace.artifacts.unrolled,
                            trace.loop_state,
                            i64::try_from(b).unwrap_or(i64::MAX),
                            kept,
                        )
                    })
                    .collect()
            }
        };
        out.push(LoweredMacro { per_block });
    }
    Ok(out)
}

/// Evaluates every sig, field, skolem and macro, per block.
fn evaluate_blocks(
    ir: &Ir,
    req: &XmlRequest<'_>,
    plan: &Plan,
    macros: &[LoweredMacro],
) -> Result<Vec<BlockValues>, TranslateError> {
    // Evaluation is an eval-position read, where the reference wraps overflow
    // silently (evaluator contract §2), so the forbid-mode guard never suppresses
    // a value the reference would have printed.
    let opts = SolveOptions {
        allow_overflow: true,
        ..req.opts
    };
    let goal = solution_goal(req);
    // Sigs and fields are keyed by the **original** relation ids in both
    // solution shapes (a trace's per-state instances are already split back
    // onto them), so they share the command's own bounds.
    let mut structural_bounds = req.bounds.bounds.clone();
    // The macro fragments of a temporal command resolve to the **per-state
    // copies** instead, which only the flat instance carries — so they get
    // their own evaluator over the unrolled bounds (the REPL's own split).
    let mut macro_bounds = match req.solution {
        XmlSolution::Static { .. } => req.bounds.bounds.clone(),
        XmlSolution::Trace { trace } => trace.artifacts.unrolled.bounds.clone(),
    };
    for (rel, bound) in &goal.skolem_bounds {
        structural_bounds.bind(*rel, bound.clone());
        macro_bounds.bind(*rel, bound.clone());
    }

    let mut blocks = Vec::with_capacity(plan.blocks);
    for b in 0..plan.blocks {
        let instance = match req.solution {
            XmlSolution::Static { instance, .. } => instance,
            XmlSolution::Trace { trace } => {
                let state = normalize_state(
                    i64::try_from(b).unwrap_or(i64::MAX),
                    plan.tracelength,
                    plan.loop_state,
                );
                &trace.states[state]
            }
        };
        let mut values = BlockValues::default();
        {
            let mut eval = Evaluator::new(
                ir,
                instance,
                req.scoped,
                &opts,
                req.bounds.int_sig,
                req.bounds.seq_int_sig,
                &structural_bounds,
            );
            for (sig, denote) in &req.bounds.sig_denote {
                values.sigs.insert(*sig, eval.eval_rel(*denote)?);
            }
            for (field, denote) in &req.bounds.field_denote {
                values.fields.insert(*field, eval.eval_rel(*denote)?);
            }
        }
        for skolem in &plan.skolems {
            let arity = ir.relations[skolem.rel].arity;
            let value = instance
                .get(skolem.rel)
                .cloned()
                .unwrap_or_else(|| TupleSet::empty(arity));
            values.skolems.insert(skolem.rel, value);
        }

        let macro_instance = match req.solution {
            XmlSolution::Static { instance, .. } => instance,
            XmlSolution::Trace { trace } => &trace.artifacts.instance,
        };
        let mut macro_eval = Evaluator::new(
            ir,
            macro_instance,
            req.scoped,
            &opts,
            req.bounds.int_sig,
            req.bounds.seq_int_sig,
            &macro_bounds,
        );
        if let XmlSolution::Trace { trace } = req.solution {
            macro_eval = macro_eval.with_loop_state(trace.loop_state);
        }
        for lowered in macros {
            let Some(&fragment) = lowered.per_block.get(b) else {
                continue;
            };
            values
                .macros
                .push(macro_value(&mut macro_eval, req, fragment)?);
        }
        blocks.push(values);
    }
    Ok(blocks)
}

/// One macro's value as a tupleset. A relational body is the ordinary case; an
/// `int`-typed body is the reference's `smallIntType`, whose `hasTuple()` holds
/// and whose evaluated value is the corresponding `Int` atom.
fn macro_value(
    eval: &mut Evaluator<'_>,
    req: &XmlRequest<'_>,
    fragment: LoweredFragment,
) -> Result<TupleSet, TranslateError> {
    match fragment {
        LoweredFragment::Rel(r) => eval.eval_rel(r),
        LoweredFragment::Int(i) => {
            let (value, _overflow) = eval.eval_int(i)?;
            let mut ts = TupleSet::empty(1);
            if let Some(atom) = int_atom(req.scoped, value) {
                ts.insert(Tuple::new(vec![atom]));
            }
            Ok(ts)
        }
        // A Boolean body is a `pred`, which `collect_macros` already excluded
        // via the reference's `hasTuple()` gate (§6).
        LoweredFragment::Formula(_) => Ok(TupleSet::empty(1)),
    }
}

/// The universe atom holding integer `value`, or `None` when it lies outside
/// the command's bitwidth.
fn int_atom(scoped: &ScopedUniverse, value: i64) -> Option<AtomId> {
    let half = 1i64.checked_shl(scoped.bitwidth.checked_sub(1)?)?;
    let offset = usize::try_from(value.checked_add(half)?).ok()?;
    (offset < scoped.int_atom_count).then(|| AtomId::from_index(scoped.sig_atom_count + offset))
}

// -------------------------------------------------------------- the ID map

/// What an `ID=` can name (§2/§5/§6): the three families sharing the
/// reference's single `IdentityHashMap`. Macro skolems are **not** here — they
/// use the separate `m<i>` namespace.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum XmlKey {
    Sig(SigId),
    Field(FieldId),
    Skolem(RelId),
}

/// The reference's lazy-memoized `map(Expr)` (§2), keyed by id rather than by
/// object identity: `id = map.size()` on first touch, never reassigned.
#[derive(Debug, Default)]
struct Ids {
    map: BTreeMap<XmlKey, usize>,
}

impl Ids {
    fn get(&mut self, key: XmlKey) -> usize {
        let next = self.map.len();
        *self.map.entry(key).or_insert(next)
    }
}

// ----------------------------------------------------------- block writer

/// One `<instance>` block's rendering pass.
struct BlockWriter<'a> {
    world: &'a ResolvedWorld,
    plan: &'a Plan,
    values: &'a BlockValues,
    universe: &'a Universe,
    ids: Ids,
    out: &'a mut String,
}

impl BlockWriter<'_> {
    /// The per-state driver, in the reference constructor's own order: the
    /// `<instance>` header (§1), the `univ` recursion, the subset sigs, the
    /// ordinary skolems, the macro skolems, `</instance>`.
    fn write_block(mut self, req: &XmlRequest<'_>) {
        let plan = self.plan;
        let _ = write!(
            self.out,
            "<instance bitwidth=\"{}\" maxseq=\"{}\" mintrace=\"{}\" maxtrace=\"{}\" command=\"",
            req.scoped.bitwidth, req.scoped.maxseq, plan.mintrace, plan.maxtrace
        );
        escape_into(self.out, &plan.command_text);
        self.out.push_str("\" filename=\"");
        escape_into(self.out, req.filename);
        let _ = writeln!(
            self.out,
            "\" tracelength=\"{}\" looplength=\"{}\">",
            plan.tracelength,
            plan.tracelength - plan.loop_state
        );

        self.write_sig(self.world.builtins.univ);
        for &subset in &plan.subsets {
            self.write_sig(subset);
        }
        for skolem in &plan.skolems {
            self.write_skolem(skolem);
        }
        for index in 0..plan.macros.len() {
            self.write_macro_skolem(index);
        }
        self.out.push_str("\n</instance>\n");
    }

    /// `writeSig` (§2/§3): recurse into the children first, print this sig's
    /// tag, print the atoms no descendant already claimed, then interleave this
    /// sig's fields. Returns this sig's **own, pre-subtraction** value — what
    /// the caller accumulates.
    fn write_sig(&mut self, sig: SigId) -> TupleSet {
        let world = self.world;
        let plan = self.plan;
        let univ = world.builtins.univ;
        if sig == world.builtins.none {
            return TupleSet::empty(1);
        }
        let is_prim = matches!(world.sigs[sig].kind, SigKind::Prim { .. });
        let mut claimed = TupleSet::empty(1);
        if is_prim {
            for i in 0..plan.children_of(sig, univ).len() {
                let kid = plan.children_of(sig, univ)[i];
                let ts = self.write_sig(kid);
                claimed = union(&claimed, &ts);
            }
        }

        let s = &world.sigs[sig];
        self.out.push_str("\n<sig label=\"");
        escape_into(self.out, sig_label(world, sig));
        self.out.push_str("\" ID=\"");
        let id = self.ids.get(XmlKey::Sig(sig));
        let _ = write!(self.out, "{id}\"");
        if sig != univ {
            if let SigKind::Prim { parent: Some(p) } = s.kind {
                let pid = self.ids.get(XmlKey::Sig(p));
                let _ = write!(self.out, " parentID=\"{pid}\"");
            }
        }
        // Attribute order is the reference's exactly (§3); each is bare
        // presence — `attr="yes"`, never `attr="no"`.
        if s.is_builtin {
            self.out.push_str(" builtin=\"yes\"");
        }
        if s.is_abstract {
            self.out.push_str(" abstract=\"yes\"");
        }
        match s.mult {
            Some(SigMult::One) => self.out.push_str(" one=\"yes\""),
            Some(SigMult::Lone) => self.out.push_str(" lone=\"yes\""),
            Some(SigMult::Some) => self.out.push_str(" some=\"yes\""),
            None => {}
        }
        if s.is_private {
            self.out.push_str(" private=\"yes\"");
        }
        if let SigKind::Subset { exact: true, .. } = s.kind {
            self.out.push_str(" exact=\"yes\"");
        }
        if s.is_enum {
            self.out.push_str(" enum=\"yes\"");
        }
        if s.is_var {
            self.out.push_str(" var=\"yes\"");
        }
        self.out.push_str(">\n");

        // `univ`/`Int`/`seq/Int` structurally never get `<atom>` children (§3);
        // `String` — the one builtin that does — takes the ordinary path.
        let skips_atoms = sig == univ || sig == world.builtins.int || sig == world.builtins.seq_int;
        let own = if skips_atoms {
            TupleSet::empty(1)
        } else {
            let own = self
                .values
                .sigs
                .get(&sig)
                .cloned()
                .unwrap_or_else(|| TupleSet::empty(1));
            let universe = self.universe;
            for tuple in minus(&own, &claimed).iter() {
                self.out.push_str("   <atom label=\"");
                if let Some(atom) = tuple.atoms().first() {
                    escape_into(self.out, universe.name(*atom));
                }
                self.out.push_str("\"/>\n");
            }
            own
        };

        // A subset sig's parents are the multi-parent encoding (§3): no
        // `parentID`, one `<type>` child each.
        if let SigKind::Subset { parents, .. } = &world.sigs[sig].kind {
            for &parent in parents {
                let pid = self.ids.get(XmlKey::Sig(parent));
                let _ = writeln!(self.out, "   <type ID=\"{pid}\"/>");
            }
        }
        self.out.push_str("</sig>\n");

        for i in 0..world.sigs[sig].fields.len() {
            self.write_field(world.sigs[sig].fields[i]);
        }
        own
    }

    /// `writeField` (§5). A field whose declared type holds no tuple is skipped
    /// outright, exactly as the reference skips it.
    fn write_field(&mut self, field: FieldId) {
        let world = self.world;
        let f = &world.fields[field];
        if f.ty.has_no_tuple(world) {
            return;
        }
        self.out.push_str("\n<field label=\"");
        escape_into(self.out, &f.name);
        let id = self.ids.get(XmlKey::Field(field));
        let owner = self.ids.get(XmlKey::Sig(world.fields[field].owner));
        let _ = write!(self.out, "\" ID=\"{id}\" parentID=\"{owner}\"");
        let f = &world.fields[field];
        if f.is_private {
            self.out.push_str(" private=\"yes\"");
        }
        if f.is_var {
            self.out.push_str(" var=\"yes\"");
        }
        self.out.push_str(">\n");
        let tuples = self
            .values
            .fields
            .get(&field)
            .cloned()
            .unwrap_or_else(|| TupleSet::empty(1));
        let types = fold(world, &world.fields[field].ty);
        self.write_expr(&tuples, &types);
        self.out.push_str("</field>\n");
    }

    /// `writeSkolem` for an ordinary existential witness (§6).
    fn write_skolem(&mut self, skolem: &SkolemDef) {
        let tuples = self
            .values
            .skolems
            .get(&skolem.rel)
            .cloned()
            .unwrap_or_else(|| TupleSet::empty(skolem.types.len().max(1)));
        self.out.push_str("\n<skolem label=\"");
        escape_into(self.out, &skolem.name);
        let id = self.ids.get(XmlKey::Skolem(skolem.rel));
        let _ = writeln!(self.out, "\" ID=\"{id}\">");
        let types = [skolem.types.clone()];
        self.write_expr(&tuples, &types);
        self.out.push_str("</skolem>\n");
    }

    /// A macro skolem (§6): the `m<i>` namespace, entirely separate from the
    /// shared map the three families above use.
    fn write_macro_skolem(&mut self, index: usize) {
        let world = self.world;
        let m = &self.plan.macros[index];
        let tuples = self
            .values
            .macros
            .get(index)
            .cloned()
            .unwrap_or_else(|| TupleSet::empty(1));
        self.out.push_str("\n<skolem label=\"");
        escape_into(self.out, &m.label);
        let _ = write!(self.out, "\" ID=\"m{index}\"");
        if m.private {
            self.out.push_str(" private=\"yes\"");
        }
        self.out.push_str(">\n");
        let types = fold(world, &world.funcs[m.func].return_ty);
        self.write_expr(&tuples, &types);
        self.out.push_str("</skolem>\n");
    }

    /// `writeExpr`'s body (§5): `<tuple>`s only when the relation is nonempty,
    /// `<types>` always — one per folded product of the declared type.
    fn write_expr(&mut self, tuples: &TupleSet, types: &[Vec<SigId>]) {
        let universe = self.universe;
        for tuple in tuples.iter() {
            self.out.push_str("   <tuple>");
            for atom in tuple.atoms() {
                self.out.push_str(" <atom label=\"");
                escape_into(self.out, universe.name(*atom));
                self.out.push_str("\"/>");
            }
            self.out.push_str(" </tuple>\n");
        }
        for columns in types {
            self.out.push_str("   <types>");
            for &col in columns {
                let id = self.ids.get(XmlKey::Sig(col));
                let _ = write!(self.out, " <type ID=\"{id}\"/>");
            }
            self.out.push_str(" </types>\n");
        }
    }
}

// ---------------------------------------------------------------- utilities

/// A sig's `label=` (§3): the builtins keep their bare labels (`univ`, `Int`,
/// `seq/Int`, `String`), every other sig uses its global label.
fn sig_label(world: &ResolvedWorld, sig: SigId) -> &str {
    let s = &world.sigs[sig];
    if s.is_builtin {
        &s.name
    } else {
        &s.qualified_name
    }
}

fn union(a: &TupleSet, b: &TupleSet) -> TupleSet {
    let mut out = a.clone();
    for t in b.iter() {
        out.insert(t.clone());
    }
    out
}

fn minus(a: &TupleSet, b: &TupleSet) -> TupleSet {
    let mut out = TupleSet::empty(a.arity());
    for t in a.iter() {
        if !b.contains(t) {
            out.insert(t.clone());
        }
    }
    out
}

/// The column sigs an ordinary skolem's `<types>` reports.
///
/// The reference reads the witness's declared `Type` off its `ExprVar`;
/// mettle's skolem relations carry a name, an arity and a **bound** instead
/// (`als_core::lower`'s `alloc_skolem`), so each column's sig is derived from
/// the atoms its upper bound admits: the least common prim ancestor of their
/// minting sigs, `univ` in the limit. Always a sound over-approximation of the
/// declared type, never a narrower claim.
fn bound_types(world: &ResolvedWorld, universe: &Universe, upper: &TupleSet) -> Vec<SigId> {
    (0..upper.arity())
        .map(|column| {
            let mut acc: Option<SigId> = None;
            for tuple in upper.iter() {
                let Some(&atom) = tuple.atoms().get(column) else {
                    continue;
                };
                let sig = atom_sig(world, universe, atom);
                acc = Some(match acc {
                    None => sig,
                    Some(prev) => least_common_prim(world, prev, sig),
                });
            }
            acc.unwrap_or(world.builtins.univ)
        })
        .collect()
}

/// The sig an atom's name says it belongs to: `String` for a quoted atom, `Int`
/// for a bare numeral, else the sig whose bare label prefixes `Label$N`.
fn atom_sig(world: &ResolvedWorld, universe: &Universe, atom: AtomId) -> SigId {
    let name = universe.name(atom);
    if name.starts_with('"') {
        return world.builtins.string;
    }
    let Some((label, _)) = name.rsplit_once('$') else {
        return world.builtins.int;
    };
    for (id, sig) in world.sigs.iter() {
        if sig.is_builtin {
            continue;
        }
        let bare = sig
            .qualified_name
            .strip_prefix("this/")
            .unwrap_or(&sig.qualified_name);
        if bare == label {
            return id;
        }
    }
    world.builtins.univ
}

/// The nearest prim sig that is an ancestor of (or equal to) both.
fn least_common_prim(world: &ResolvedWorld, a: SigId, b: SigId) -> SigId {
    let mut cur = a;
    loop {
        if world.is_same_or_descendent(b, cur) {
            return cur;
        }
        match world.sigs[cur].kind {
            SigKind::Prim { parent: Some(p) } => cur = p,
            SigKind::Prim { parent: None } | SigKind::Subset { .. } => return world.builtins.univ,
        }
    }
}

/// `Type.fold()` (bytecode-pinned, mt-071): one column list per product entry,
/// with entries differing in exactly one column collapsed onto that column's
/// **abstract** parent when — and only when — every one of that parent's
/// children is present.
fn fold(world: &ResolvedWorld, ty: &Type) -> Vec<Vec<SigId>> {
    let mut ans: Vec<Vec<SigId>> = Vec::new();
    for entry in &ty.entries {
        let mut columns = entry.0.clone();
        loop {
            let mut changed = false;
            let mut i = 0;
            while i < columns.len() {
                let foldable = match world.sigs[columns[i]].kind {
                    SigKind::Prim { parent: Some(p) } => {
                        p != world.builtins.univ && world.sigs[p].is_abstract
                    }
                    SigKind::Prim { parent: None } | SigKind::Subset { .. } => false,
                };
                if foldable {
                    if let Some(next) = fold_column(world, &mut ans, &columns, i) {
                        columns = next;
                        changed = true;
                        continue;
                    }
                }
                i += 1;
            }
            if !changed {
                break;
            }
        }
        ans.push(columns);
    }
    ans
}

/// One folding step: collapse `columns[i]` onto its abstract parent when every
/// sibling is accounted for among the already-folded entries.
fn fold_column(
    world: &ResolvedWorld,
    ans: &mut Vec<Vec<SigId>>,
    columns: &[SigId],
    i: usize,
) -> Option<Vec<SigId>> {
    let SigKind::Prim {
        parent: Some(parent),
    } = world.sigs[columns[i]].kind
    else {
        return None;
    };
    let mut siblings: Vec<SigId> = world
        .sigs
        .iter()
        .filter(|(_, s)| matches!(s.kind, SigKind::Prim { parent: Some(p) } if p == parent))
        .map(|(id, _)| id)
        .collect();
    let mut absorbed: Vec<usize> = Vec::new();
    for j in (0..ans.len()).rev() {
        let other = &ans[j];
        if other.len() != columns.len() {
            continue;
        }
        let matched = other.iter().enumerate().all(|(k, &col)| {
            if k == i {
                matches!(world.sigs[col].kind, SigKind::Prim { parent: Some(p) } if p == parent)
            } else {
                col == columns[k]
            }
        });
        if matched {
            absorbed.push(j);
            if let Some(pos) = siblings.iter().position(|&s| s == other[i]) {
                siblings.remove(pos);
            }
        }
    }
    if let Some(pos) = siblings.iter().position(|&s| s == columns[i]) {
        siblings.remove(pos);
    }
    if !siblings.is_empty() {
        return None;
    }
    // `absorbed` is descending, so index-based removal stays valid.
    for &j in &absorbed {
        ans.remove(j);
    }
    if let Some(pos) = ans.iter().position(|e| e.as_slice() == columns) {
        ans.remove(pos);
    }
    let mut out = columns.to_vec();
    out[i] = parent;
    Some(out)
}

/// The reference's 5-entity XML escaping plus numeric character references for
/// everything outside printable ASCII (§8) — the `&#x000a;` newline form the
/// probes pinned, generalized over the whole non-printable range the way
/// `Util.encodeXML`'s own `char` loop generalizes it (UTF-16 code units,
/// because that is the unit a Java `char` is).
fn escape_into(out: &mut String, text: &str) {
    let mut buf = [0u16; 2];
    for c in text.chars() {
        match c {
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '&' => out.push_str("&amp;"),
            '\'' => out.push_str("&apos;"),
            '"' => out.push_str("&quot;"),
            ' '..='~' => out.push(c),
            _ => {
                for unit in c.encode_utf16(&mut buf) {
                    let _ = write!(out, "&#x{unit:04x};");
                }
            }
        }
    }
}

// --------------------------------------------------------- the command text

/// The `command=` attribute (§1): `"Run "`/`"Check "` plus the reference's
/// `Command.toString()`, reproduced from that method's bytecode.
///
/// **A per-sig scope clause names the sig by its bare declared name** — `2 P`,
/// never `2 this/P`, and `2 S` for a sig opened from another module, never
/// `2 sub/S` or `2 dm/T`. §1.2 of `alloy6-instance-xml.md` reads the
/// bytecode's `sig.label` as the qualified label; live jar probes say
/// otherwise, on all three shapes (mt-132, `scratchpad/probe/mt132/`:
/// `Cmd1`/`Cmd2`/`Cmd3` — writing the scope target as `this/P` or `sub/S` in
/// the source does not change what the jar prints either). Everything else in
/// this function still follows §1.2.
///
/// One clause shape stays unmatched: a range or increment scope
/// (`for 3 but 1..3 P`) prints its **upper** endpoint in the jar (`3 P`) and
/// its lower one here (`1 P`), because `CommandScope` keeps only the starting
/// value. Both engines still solve at the low end, so the verdicts agree
/// (mt-132, `Cmd4`/`Cmd5`/`CmdR`); see `LIMITATIONS.md`.
fn command_text(world: &ResolvedWorld, graph: &ModuleGraph, index: usize) -> String {
    let cmd = &world.commands[index];
    let mut out = String::from(match cmd.kind {
        CmdKind::Run => "Run ",
        CmdKind::Check => "Check ",
    });
    out.push_str(&command_label(world, graph, index));

    let overall = cmd.overall.map_or(-1, i64::from);
    let bitwidth = cmd.bitwidth.map_or(-1, i64::from);
    let maxseq = cmd.maxseq.map_or(-1, i64::from);
    // `minprefix`/`maxprefix` **as written**, already collapsed by `exactly` —
    // exactly the jar's own `Command` construction (probe X-03's `3..3 steps`).
    let (minprefix, maxprefix) = cmd.steps.map_or((-1, -1), |s| {
        (
            s.min.map_or(-1, i64::from),
            match s.max {
                StepsMax::Bounded(n) => i64::from(n),
                StepsMax::Unbounded => i64::from(i32::MAX),
            },
        )
    });
    let decorated =
        bitwidth >= 0 || maxseq >= 0 || !cmd.scopes.is_empty() || minprefix >= 0 || maxprefix >= 0;
    if overall >= 0 && decorated {
        let _ = write!(out, " for {overall} but");
    } else if overall >= 0 {
        let _ = write!(out, " for {overall}");
    } else if decorated {
        out.push_str(" for");
    }

    let mut first = true;
    if bitwidth >= 0 {
        let _ = write!(out, " {bitwidth} int");
        first = false;
    }
    if maxseq >= 0 {
        out.push_str(if first { " " } else { ", " });
        let _ = write!(out, "{maxseq} seq");
        first = false;
    }
    if maxprefix >= 0 {
        out.push(' ');
        if minprefix >= 0 {
            let _ = write!(out, "{minprefix}..");
        }
        if maxprefix != i64::from(i32::MAX) {
            let _ = write!(out, "{maxprefix}");
        }
        out.push_str(" steps");
        first = false;
    }
    for scope in &cmd.scopes {
        out.push_str(if first { " " } else { ", " });
        if scope.is_exact {
            out.push_str("exactly ");
        }
        let _ = write!(out, "{} {}", scope.scope, world.sigs[scope.sig].name);
        first = false;
    }
    match cmd.expect {
        Some(Expect::Sat) => out.push_str(" expect 1"),
        Some(Expect::Unsat) => out.push_str(" expect 0"),
        Some(Expect::Other(n)) => {
            let _ = write!(out, " expect {n}");
        }
        None => {}
    }
    out
}

/// The command's own label, as the reference builds it
/// (`CompModule.addCommand`): the written `label:` prefix, else the run/check
/// target's name, else the synthesized `run$<n>`/`check$<n>` where `n` is the
/// 1-based position of the command among its own module's commands.
fn command_label(world: &ResolvedWorld, graph: &ModuleGraph, index: usize) -> String {
    let cmd = &world.commands[index];
    if let Some(label) = &cmd.label {
        if !label.is_empty() {
            return label.clone();
        }
    }
    match &cmd.target {
        CmdTargetResolved::Named(funcs) => {
            if let Some(&f) = funcs.first() {
                return world.funcs[f].name.clone();
            }
        }
        CmdTargetResolved::Assert { body, module } => {
            if let Some(name) = assert_name(graph, *module, *body) {
                return name;
            }
        }
        CmdTargetResolved::Block { .. } | CmdTargetResolved::Unresolved => {}
    }
    let file = cmd.span.file;
    let position = world.commands[..index]
        .iter()
        .filter(|c| c.span.file == file)
        .count();
    match cmd.kind {
        CmdKind::Run => format!("run${}", position + 1),
        CmdKind::Check => format!("check${}", position + 1),
    }
}

/// Recovers a checked assertion's declared name from its module's AST (the
/// resolved command keeps only `(body, module)`).
fn assert_name(graph: &ModuleGraph, module: ModuleId, body: ExprId) -> Option<String> {
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
