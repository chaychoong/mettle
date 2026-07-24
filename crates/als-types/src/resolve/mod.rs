//! The Rung-2 name resolver + type checker (bead mt-018): turns the mt-017
//! [`ModuleGraph`] into a resolved, type-checked [`ResolvedWorld`], reproducing
//! the reference `CompModule.resolveAll` **accept/reject** verdict
//! (resolution-doc §1 pipeline, ADR-0008).
//!
//! ## Structure (ADR-0008 decision 4, with one documented deviation)
//! The reference runs a bottom-up bounding-type pass then a top-down
//! `resolve(relevantType)` pass. mettle keeps that ordering *semantically* — a
//! node's children are fully typed bottom-up before the node resolves its own
//! overload choice against the relevant type pushed from its parent — but folds
//! them into one bidirectional walk ([`expr::check`]) rather than materializing
//! a separate typed tree. The ADR listed a *fused* walk as rejected; the fusion
//! here preserves the ADR's stated invariant (candidate types are complete
//! before a choice is resolved) because recursion finishes children first. This
//! is flagged for tech-lead review: it is an accept/reject-equivalent
//! simplification, not a semantic change.
//!
//! ## Phase pipeline (resolution-doc §1)
//! Phases run in order over **every module instance** (each parametric
//! instance is resolved separately with its params substituted, matching the
//! reference's per-instance `CompModule`s). Errors are collected and the
//! **first by source position** is surfaced as the `Err` (ADR-0008 decision 7);
//! warnings never flip the verdict (§0/§5.3).

mod expr;
mod members;
mod sigs;

use als_syntax::ast::{Ast, BinOp, ExprId, ExprKind, SigMult};
use als_syntax::{Arena, ArenaId};
use indexmap::IndexMap;

use crate::choice::{BuiltinCall, ExprChoice, NameChoice, SpineChoice};
use crate::error::ResolveError;
use crate::graph::{ModuleGraph, ModuleId};
use crate::ty::Type;
use crate::warning::ResolveWarning;
use crate::world::{
    Builtins, FieldId, FuncId, MacroId, OrderingInstance, ResolvedWorld, SigId, SigKind,
};

/// The successful output of [`resolve`]: the resolved world plus the
/// (never-fatal) warnings, ordered by source `Span` (resolution-doc §8).
#[derive(Debug)]
pub struct Resolved {
    /// The resolved, type-checked world.
    pub world: ResolvedWorld,
    /// Warnings collected during resolution (secondary to the verdict).
    pub warnings: Vec<ResolveWarning>,
}

/// Resolves and type-checks a loaded module graph (resolution-doc §1).
///
/// Returns [`Resolved`] on ACCEPT, or the first-by-source-position
/// [`ResolveError`] on REJECT. Warnings are attached to the `Ok` value and
/// never turn a success into a failure (the mt-020 gauge contract).
///
/// # Errors
/// Any [`ResolveError`] from the §5.1 reject taxonomy.
pub fn resolve(graph: &ModuleGraph) -> Result<Resolved, ResolveError> {
    let mut r = Resolver::new(graph);
    r.run();
    r.finish()
}

/// Strips a leading `this/` qualifier from a name's segments (resolution-doc
/// §2.4 `Util.tailThis`): `this/plus` resolves as bare `plus`.
pub(super) fn strip_this(segs: Vec<String>) -> Vec<String> {
    if segs.len() > 1 && segs[0] == "this" {
        segs[1..].to_vec()
    } else {
        segs
    }
}

/// Per-module symbol tables (insertion order = declaration order, ADR-0008
/// decision 2). Lookups iterate in this order for deterministic candidate
/// collection (STYLE D2/C2).
#[derive(Debug, Default)]
struct ModuleSyms {
    /// Sigs declared in this module (enum members included), by bare label.
    sigs: IndexMap<String, SigId>,
    /// Module parameters bound to their argument sigs (resolution-doc §2.3),
    /// looked up like sigs in this module.
    param_sigs: IndexMap<String, SigId>,
    /// Funcs/preds by bare name — an **overload set** (resolution-doc §3.5).
    funcs: IndexMap<String, Vec<FuncId>>,
    /// Assert names declared here (for `check` target lookup + dup reject).
    asserts: IndexMap<String, als_syntax::Span>,
    /// Macros by name.
    macros: IndexMap<String, MacroId>,
}

/// The resolver's working state: the graph, the world being built, per-module
/// symbol tables, reachability, and the diagnostic sinks.
struct Resolver<'g> {
    graph: &'g ModuleGraph,
    world: ResolvedWorld,
    /// Symbol tables, indexed by `ModuleId::index`.
    mods: Vec<ModuleSyms>,
    /// Name-reachable modules per module (self + non-private transitive opens),
    /// indexed by `ModuleId::index`; the scope-chain search order.
    reachable: Vec<Vec<ModuleId>>,
    /// Per-user-sig source records (parent spec, owned field decls, appended
    /// fact), threaded from sig registration into the field/fact passes.
    sig_srcs: Vec<sigs::SigSrc>,
    /// Func/pred source records: `(id, module, paragraph)`, threaded from
    /// member registration into the decl/body passes.
    func_srcs: Vec<(FuncId, ModuleId, als_syntax::ast::ParaId)>,
    /// Root-module header parameters marked `exactly`, materialized as
    /// top-level sigs (`register_root_param_sigs`). The reference's
    /// `CompModule.addModelName` adds these directly to `exactSigs` at
    /// header-parse time, independent of any command's own scope clause
    /// (mt-041, probe row 7); `resolve_ordering` part (a) folds them into every
    /// command's `additional_exact`.
    root_exact_sigs: Vec<SigId>,
    errors: Vec<ResolveError>,
    warnings: Vec<ResolveWarning>,
}

impl<'g> Resolver<'g> {
    fn new(graph: &'g ModuleGraph) -> Self {
        let module_count = graph.modules.len();
        let world = ResolvedWorld {
            sigs: Arena::new(),
            fields: Arena::new(),
            funcs: Arena::new(),
            macros: Arena::new(),
            commands: Vec::new(),
            facts: Vec::new(),
            choices: crate::choice::ChoiceTable::new(),
            ordering: Vec::new(),
            // Placeholder builtins; seeded first thing in `run`.
            builtins: Builtins {
                univ: SigId::from_index(0),
                int: SigId::from_index(0),
                seq_int: SigId::from_index(0),
                string: SigId::from_index(0),
                none: SigId::from_index(0),
            },
        };
        Resolver {
            graph,
            world,
            mods: (0..module_count).map(|_| ModuleSyms::default()).collect(),
            reachable: Vec::new(),
            sig_srcs: Vec::new(),
            func_srcs: Vec::new(),
            root_exact_sigs: Vec::new(),
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Runs the phase pipeline (resolution-doc §1). Each phase group bails early
    /// (via `has_errors`) when the reference would have thrown at that
    /// checkpoint, so later phases never see a half-built world.
    fn run(&mut self) {
        self.seed_builtins();
        self.compute_reachable();

        // Phase 4a: register sigs + enum desugaring (names, quals, kinds).
        self.register_sigs();
        // Fill each sig's global label (the atom-naming prefix) from the module
        // alias graph — needed by `als_core::scope` (mt-029).
        self.compute_qualified_names();
        // Phase 2/3-equivalent: bind module params to argument sigs.
        self.resolve_params();
        // Phase 4b: resolve sig parents, detect cycles, compute types.
        self.resolve_sig_hierarchy();
        if self.has_errors() {
            return;
        }

        // Register func/pred + assert + macro names (dup checks) before bodies.
        self.register_members();
        if self.has_errors() {
            return;
        }

        // Phase 5: non-defined fields.
        self.resolve_fields(false);
        // Phase 6: func/pred decls (params + return types).
        self.resolve_func_decls();
        // Phase 7: defined (`=`) fields (may reference other fields/funcs).
        self.resolve_fields(true);
        if self.has_errors() {
            return;
        }
        // Phase 9: field-name clash across overlapping sigs.
        self.reject_name_clash();
        if self.has_errors() {
            return;
        }

        // Phase 10: func/pred bodies, asserts, facts.
        self.resolve_bodies();
        if self.has_errors() {
            return;
        }
        // Phase 11: commands (targets + scopes).
        self.resolve_commands();

        // mt-035 (LEDGER-004): `util/ordering` exact-scope propagation + the
        // ordering-instance seam the bounds phase pins `first`/`next` from. Purely
        // additive metadata — the accept/reject verdict + warnings are unchanged
        // (invariance rule), so it runs even after the early-bail checkpoints.
        self.resolve_ordering();
    }

    /// Populates the `util/ordering` exact-scope + pinning seam (mt-035,
    /// LEDGER-004, translation-ref §5).
    ///
    /// **Part (a) — exact scope.** Any module parameter marked `exactly` (the
    /// reference's `additionalExactScopes` mechanism, jar-verified general — not
    /// ordering-specific) forces its argument sig to an exact scope. `util/
    /// ordering[exactly elem]` is the one stdlib module that uses it (enums
    /// auto-open it), but a user module `foo[exactly x]` behaves identically. A
    /// **root** module's own `exactly` header params are materialized as
    /// top-level sigs and marked exact directly (mt-041, `addModelName`
    /// root path; probe row 7), carried here in [`Self::root_exact_sigs`]. Every
    /// command gets the same set; the scope layer already honors
    /// [`ResolvedCommand::additional_exact`].
    ///
    /// **Part (b) — the pinning seam.** The trigger is **syntactic**, not
    /// module-identity based (mt-041, probe matrix): a resolved reserved
    /// `pred/totalOrder[S, F, N]` box-join (the grammar's context-sensitive
    /// `pred/totalOrder` keyword, not an ordinary predicate call) appearing as a
    /// top-level conjunct of the appended fact of a **`one` sig**, with `S` a sig
    /// and `F`/`N` the `one` sig's **own** fields (the stdlib `Ord` shape).
    /// Renaming the module, sig, or fields keeps it detected (rows 2–5);
    /// expressing the same order without the keyword does not (row 6). The stdlib
    /// `util/ordering` path — opened, aliased, enum-auto-opened, or run as the
    /// root file — all carry this fact, so all are caught. The bounds phase reads
    /// [`ResolvedWorld::ordering`] to pin `first`/`next` when eligible.
    ///
    /// This under-approximates the jar's own trigger (`first`/`next`/`elem` all
    /// translating to plain Kodkod `Relation`s): only the `one`-sig-owns-its-own-
    /// fields shape, where `this` is a fixed singleton so the args ARE plain
    /// relations, is matched. Two jar-firing spellings are deliberately not
    /// matched — a `pred/totalOrder` fact inside a plural subsig of a `one` sig
    /// (`this` ranges, args are not plain relations there anyway), and a
    /// module-level `fact { pred/totalOrder[S, Ord.First, Ord.Next] }` with
    /// explicit qualification. Both are unprobed, have zero corpus incidence, and
    /// are count-only (the hand-built `pred/totalOrder` formula still governs the
    /// verdict), so the miss is conservative.
    fn resolve_ordering(&mut self) {
        // Part (a): collect every exactly-param argument sig, deterministically.
        let mut exact: Vec<SigId> = Vec::new();
        for m in 0..self.graph.modules.len() {
            let mid = ModuleId::from_index(m);
            for binding in &self.graph.modules[mid].params {
                if binding.is_exact {
                    if let Some(&sig) = self.mods[m].param_sigs.get(&binding.param) {
                        exact.push(sig);
                    }
                }
            }
        }
        exact.extend(self.root_exact_sigs.iter().copied());
        exact.sort_unstable_by_key(|s| s.index());
        exact.dedup();
        for cmd in &mut self.world.commands {
            cmd.additional_exact.clone_from(&exact);
        }

        // Part (b): structural detection of the `pred/totalOrder[S, F, N]` seam.
        self.world.ordering = self.collect_ordering_instances();
    }

    /// Scans every `one` sig's appended fact (in `SigId` order) for the reserved
    /// `pred/totalOrder[S, F, N]` shape over the sig's own fields, returning the
    /// detected instances deduped and in a deterministic order (mt-041 part (b)).
    /// Only `one` sigs can carry a pinnable instance — a fixed singleton `this`
    /// is what makes `F`/`N` translate to plain relations in the jar — so plural
    /// sigs are skipped outright.
    fn collect_ordering_instances(&self) -> Vec<OrderingInstance> {
        let mut instances: Vec<OrderingInstance> = Vec::new();
        for (sid, sig) in self.world.sigs.iter() {
            if sig.mult != Some(SigMult::One) {
                continue;
            }
            if let Some(body) = sig.appended_fact {
                self.scan_ordering_conjuncts(sig.module, sid, body, &mut instances);
            }
        }
        instances.sort_unstable_by_key(|i| (i.elem.index(), i.first.index(), i.next.index()));
        instances.dedup();
        instances
    }

    /// Descends the **top-level conjuncts** of `owner`'s appended fact (blocks
    /// and `&&`), pushing an [`OrderingInstance`] for each reserved
    /// `pred/totalOrder` call found among them. A `pred/totalOrder` buried under
    /// a quantifier or a disjunction is not a top-level constraint the bounds
    /// phase can pin, so it is not descended into.
    fn scan_ordering_conjuncts(
        &self,
        module: ModuleId,
        owner: SigId,
        body: ExprId,
        out: &mut Vec<OrderingInstance>,
    ) {
        match &self.ast(module).exprs[body].kind {
            ExprKind::Block(items) => {
                for &item in items {
                    self.scan_ordering_conjuncts(module, owner, item, out);
                }
            }
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                self.scan_ordering_conjuncts(module, owner, *lhs, out);
                self.scan_ordering_conjuncts(module, owner, *rhs, out);
            }
            ExprKind::BoxJoin { args, .. } => {
                if let Some(inst) = self.match_total_order(module, owner, body, args) {
                    out.push(inst);
                }
            }
            _ => {}
        }
    }

    /// Matches a box-join node against the reserved `pred/totalOrder[S, F, N]`
    /// shape: the node resolved to [`BuiltinCall::TotalOrder`] (the same
    /// recognition `als_core::lower` consumes — the grammar keyword, not an
    /// ordinary `totalOrder` predicate, so probe row 6 does not match), with
    /// three arguments — a sig `S`, and `F`/`N` fields **owned by `owner`
    /// itself** (the `one` sig whose fact this is). Requiring own-fields, not
    /// merely fields of some `one` ancestor, keeps a `pred/totalOrder` in a
    /// plural subsig's fact (where `this` ranges and the args are not plain
    /// relations) from wrongly pinning.
    fn match_total_order(
        &self,
        module: ModuleId,
        owner: SigId,
        node: ExprId,
        args: &[ExprId],
    ) -> Option<OrderingInstance> {
        if !matches!(
            self.world.choices.get(module, node),
            Some(ExprChoice::Spine(SpineChoice::Builtin {
                op: BuiltinCall::TotalOrder,
            }))
        ) {
            return None;
        }
        let [a_elem, a_first, a_next] = args else {
            return None;
        };
        let elem = match self.world.choices.get(module, *a_elem) {
            Some(ExprChoice::Name(NameChoice::Sig(s))) => *s,
            _ => return None,
        };
        let first = self.own_field_arg(module, owner, *a_first)?;
        let next = self.own_field_arg(module, owner, *a_next)?;
        Some(OrderingInstance { elem, first, next })
    }

    /// The [`FieldId`] an argument resolves to when it is a bare implicit-`this`
    /// reference to a field `owner` **declares itself** — the shape the stdlib
    /// `one sig Ord` appended fact spells `First`/`Next` (mt-041). A field
    /// inherited from an ancestor, or any non-field, returns `None`.
    fn own_field_arg(&self, module: ModuleId, owner: SigId, arg: ExprId) -> Option<FieldId> {
        let Some(ExprChoice::Name(NameChoice::Field {
            field,
            implicit_this: true,
        })) = self.world.choices.get(module, arg)
        else {
            return None;
        };
        (self.world.fields[*field].owner == owner).then_some(*field)
    }

    /// Seeds the five builtin sigs as fixed `SigId`s (resolution-doc §4.1).
    fn seed_builtins(&mut self) {
        let root = self.graph.root;
        let univ = self.alloc_builtin("univ", None, root);
        let int = self.alloc_builtin("Int", Some(univ), root);
        let seq_int = self.alloc_builtin("seq/Int", Some(int), root);
        let string = self.alloc_builtin("String", Some(univ), root);
        let none = self.alloc_builtin("none", Some(univ), root);
        self.world.builtins = Builtins {
            univ,
            int,
            seq_int,
            string,
            none,
        };
    }

    /// Fills every sig's `qualified_name` — the global label the reference
    /// names its **relations** after (translation-ref §1.4/§16.3; distinct
    /// from the atom label, translation-ref §1.3, which strips this prefix —
    /// see `als_core::scope::ScopeSolver::walk`). A root-module sig is
    /// prefixed `this/` (the reference's `A4Solution.debugExtractKInput()`
    /// spells root relations `this/Element`, `this/Node.W`); an
    /// opened-module sig is prefixed by the alias path from the root
    /// (`foo/Widget`, `a/b/Beta`). The path is the preorder DFS over `open`
    /// edges in source order (first reach wins), mirroring how the reference
    /// assigns labels during recursive module loading.
    fn compute_qualified_names(&mut self) {
        let n = self.graph.modules.len();
        // Alias-path prefixes propagate from the root using the **bare** path
        // (`mesh/`, `a/b/`) — the `this/` root marker is not part of this
        // path and must not cascade into opened-module prefixes
        // (`mesh/Vertex`, never `this/mesh/Vertex`).
        let mut prefix: Vec<Option<String>> = vec![None; n];
        prefix[self.graph.root.index()] = Some(String::new());
        let mut stack = vec![self.graph.root];
        while let Some(m) = stack.pop() {
            // `prefix[m]` is always set before `m` is pushed.
            let here = prefix[m.index()].clone().unwrap_or_default();
            // Reverse so source-order edges pop (and win first-reach) in order.
            for edge in self.graph.modules[m].opens.iter().rev() {
                let t = edge.target;
                if prefix[t.index()].is_none() {
                    prefix[t.index()] = Some(format!("{here}{}/", edge.alias));
                    stack.push(t);
                }
            }
        }
        for i in 0..self.world.sigs.len() {
            let sig = SigId::from_index(i);
            let m = self.world.sigs[sig].module;
            let here = prefix[m.index()].clone().unwrap_or_default();
            // The root module's own sigs get the jar's literal `this/`
            // relation-name marker (translation-ref §16.3); opened-module
            // sigs use only their alias path.
            let here = if m == self.graph.root {
                format!("this/{here}")
            } else {
                here
            };
            self.world.sigs[sig].qualified_name = format!("{here}{}", self.world.sigs[sig].name);
        }
    }

    fn alloc_builtin(&mut self, name: &str, parent: Option<SigId>, module: ModuleId) -> SigId {
        let span = crate::load::synthetic_span();
        let id = SigId::from_index(self.world.sigs.len());
        self.world.sigs.alloc(crate::world::ResolvedSig {
            name: name.to_owned(),
            qualified_name: name.to_owned(),
            module,
            span,
            kind: SigKind::Prim { parent },
            is_abstract: false,
            is_enum: false,
            is_var: false,
            is_private: false,
            is_builtin: true,
            mult: None,
            fields: Vec::new(),
            field_disj_groups: Vec::new(),
            appended_fact: None,
            ty: Type::unary(id),
        });
        id
    }

    /// Computes name-reachable modules per module (self + non-private
    /// transitive opens): the scope-chain search order (resolution-doc §2.5).
    fn compute_reachable(&mut self) {
        let n = self.graph.modules.len();
        let mut all = Vec::with_capacity(n);
        for m in 0..n {
            let start = ModuleId::from_index(m);
            let mut order = vec![start];
            let mut seen = vec![false; n];
            seen[m] = true;
            let mut i = 0;
            while i < order.len() {
                let cur = order[i];
                i += 1;
                for edge in &self.graph.modules[cur].opens {
                    // A private open is visible only to its own module (private
                    // bites across modules only, §2.5).
                    if edge.is_private && cur != start {
                        continue;
                    }
                    let ti = edge.target.index();
                    if !seen[ti] {
                        seen[ti] = true;
                        order.push(edge.target);
                    }
                }
            }
            all.push(order);
        }
        self.reachable = all;
    }

    /// The AST for a module instance's file.
    fn ast(&self, m: ModuleId) -> &'g Ast {
        let file = self.graph.modules[m].file;
        self.graph.files.file(file).ast_ref()
    }

    fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Records an error (first-by-position selection happens in [`finish`]).
    fn error(&mut self, err: ResolveError) {
        self.errors.push(err);
    }

    fn warn(&mut self, w: ResolveWarning) {
        self.warnings.push(w);
    }

    /// Picks the first error by source position (ADR-0008 decision 7), or
    /// returns the accepted world + span-ordered warnings.
    fn finish(mut self) -> Result<Resolved, ResolveError> {
        if let Some(err) = self
            .errors
            .into_iter()
            .min_by_key(|e| (e.span().file.index(), e.span().start))
        {
            return Err(err);
        }
        self.warnings
            .sort_by_key(|w| (w.span().file.index(), w.span().start));
        Ok(Resolved {
            world: self.world,
            warnings: self.warnings,
        })
    }
}
