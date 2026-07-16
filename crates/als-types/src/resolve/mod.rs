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

use als_syntax::ast::Ast;
use als_syntax::{Arena, ArenaId};
use indexmap::IndexMap;

use crate::error::ResolveError;
use crate::graph::{ModuleGraph, ModuleId};
use crate::ty::Type;
use crate::warning::ResolveWarning;
use crate::world::{Builtins, FuncId, MacroId, ResolvedWorld, SigId, SigKind};

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
    /// names its atoms after. A root-module sig keeps its bare name; an
    /// opened-module sig is prefixed by the alias path from the root
    /// (`foo/Widget`, `a/b/Beta`). The path is the preorder DFS over `open`
    /// edges in source order (first reach wins), mirroring how the reference
    /// assigns labels during recursive module loading.
    fn compute_qualified_names(&mut self) {
        let n = self.graph.modules.len();
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
