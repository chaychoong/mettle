//! Sig registration, enum desugaring, module-param binding, and hierarchy
//! resolution (resolution-doc §3.1, §3.2, §2.3; phases 4a/4b).

use als_syntax::ast::{Ast, DeclId, EnumDecl, ExprId, Para, QualName, SigDecl, SigParent};
use als_syntax::{ArenaId, Span};

use crate::error::ResolveError;
use crate::graph::ModuleId;
use crate::ty::Type;
use crate::warning::ResolveWarning;
use crate::world::{ResolvedSig, SigId, SigKind};

use super::Resolver;

/// The parent clause of a user sig, captured at registration and resolved in
/// the hierarchy pass.
pub(super) enum ParentSpec {
    /// Top-level sig (implicit parent `univ`).
    Top,
    /// `extends P` — resolve `P` by name.
    Extends(QualName),
    /// An enum member: parent is the already-created abstract enum sig.
    ExtendsSig(SigId),
    /// `in`/`=` subset — resolve each parent name; `exact` marks `=`.
    Subset {
        /// Parent sig references.
        parents: Vec<QualName>,
        /// `=` (exact) vs `in`.
        exact: bool,
    },
}

/// A per-user-sig source record threaded from registration into later passes.
pub(super) struct SigSrc {
    pub id: SigId,
    pub module: ModuleId,
    pub parent: ParentSpec,
    pub span: Span,
    /// Field decls owned by this sig (empty for enum sigs/members).
    pub fields: Vec<DeclId>,
    /// Appended `sig A {…} { fact }` body, if any.
    pub appended_fact: Option<ExprId>,
    /// `var` sig (for var/static warnings + scope checks).
    pub is_var: bool,
}

impl Resolver<'_> {
    /// Phase 4a: registers every sig (and desugars enums), building the
    /// per-module sig name tables and the `sig_srcs` side table. Rejects
    /// duplicate names and reserved builtin names (`dup`, resolution-doc §3.1).
    pub(super) fn register_sigs(&mut self) {
        // A parametric module resolved as the *root* (entry point) has no
        // opener to bind its params, so the reference treats each header
        // parameter as a fresh top-level sig. Materialize those first so field
        // bounds / bodies referencing `elem`/`node`/`Addr` resolve.
        self.register_root_param_sigs();

        for m in 0..self.graph.modules.len() {
            let module = ModuleId::from_index(m);
            let ast = self.ast(module);
            for &para_id in &ast.paragraphs {
                match &ast.paras[para_id] {
                    Para::Sig(decl) => self.register_sig_decl(module, decl),
                    Para::Enum(decl) => self.register_enum_decl(module, decl),
                    _ => {}
                }
            }
        }
    }

    /// Registers the root module's header parameters as top-level sigs.
    fn register_root_param_sigs(&mut self) {
        let root = self.graph.root;
        let Some(header) = &self.ast(root).header else {
            return;
        };
        let params: Vec<(String, Span)> = header
            .params
            .iter()
            .filter_map(|p| p.name.segments.last().map(|s| (s.text.clone(), s.span)))
            .collect();
        for (name, span) in params {
            if !self.mods[root.index()].sigs.contains_key(&name) {
                self.declare_sig(
                    root,
                    &name,
                    span,
                    false,
                    false,
                    false,
                    None,
                    ParentSpec::Top,
                    Vec::new(),
                    None,
                );
            }
        }
    }

    fn register_sig_decl(&mut self, module: ModuleId, decl: &SigDecl) {
        for name in &decl.names {
            let parent = match &decl.parent {
                SigParent::None => ParentSpec::Top,
                SigParent::Extends(p) => ParentSpec::Extends(p.clone()),
                SigParent::In(ps) => ParentSpec::Subset {
                    parents: ps.clone(),
                    exact: false,
                },
                SigParent::Eq(ps) => ParentSpec::Subset {
                    parents: ps.clone(),
                    exact: true,
                },
            };
            let id = self.declare_sig(
                module,
                &name.text,
                name.span,
                decl.qual.is_abstract,
                decl.qual.is_var,
                decl.qual.is_private,
                decl.qual.mult,
                parent,
                decl.fields.clone(),
                decl.fact,
            );
            let _ = id;
        }
    }

    /// Enum desugaring (resolution-doc §3.2): `enum N {A,B,…}` becomes an
    /// abstract sig `N` plus one `one sig` per member extending `N`. The
    /// synthetic `open util/ordering[N]` is materialized by the loader.
    fn register_enum_decl(&mut self, module: ModuleId, decl: &EnumDecl) {
        let parent = self.declare_sig(
            module,
            &decl.name.text,
            decl.name.span,
            true, // abstract
            false,
            false,
            None,
            ParentSpec::Top,
            Vec::new(),
            None,
        );
        // The synthetic enum parent carries `is_enum` so the scope layer can
        // reject an explicit scope on it (translation-ref §1.2).
        self.world.sigs[parent].is_enum = true;
        for variant in &decl.variants {
            self.declare_sig(
                module,
                &variant.text,
                variant.span,
                false,
                false,
                false,
                Some(als_syntax::ast::SigMult::One),
                ParentSpec::ExtendsSig(parent),
                Vec::new(),
                None,
            );
        }
    }

    /// Allocates a sig, registers its name (rejecting dups + reserved names),
    /// and records its source. Multiplicity/quals are carried through.
    #[allow(clippy::too_many_arguments)] // a sig decl genuinely carries this many independent facets
    fn declare_sig(
        &mut self,
        module: ModuleId,
        name: &str,
        span: Span,
        is_abstract: bool,
        is_var: bool,
        is_private: bool,
        mult: Option<als_syntax::ast::SigMult>,
        parent: ParentSpec,
        fields: Vec<DeclId>,
        appended_fact: Option<ExprId>,
    ) -> SigId {
        // `dup` rejects reserved builtin names and in-module duplicates.
        if matches!(name, "univ" | "Int" | "none" | "iden" | "String")
            || self.mods[module.index()].sigs.contains_key(name)
        {
            self.error(ResolveError::DuplicateSig {
                name: name.to_owned(),
                span,
            });
        }
        let id = SigId::from_index(self.world.sigs.len());
        self.world.sigs.alloc(ResolvedSig {
            name: name.to_owned(),
            // Bare name for now; `compute_qualified_names` fills the alias path.
            qualified_name: name.to_owned(),
            module,
            span,
            // Placeholder kind; the hierarchy pass fills parents + subset kind.
            kind: SigKind::Prim { parent: None },
            is_abstract,
            is_enum: false,
            is_var,
            is_private,
            is_builtin: false,
            mult,
            fields: Vec::new(),
            ty: Type::empty(),
        });
        self.mods[module.index()]
            .sigs
            .entry(name.to_owned())
            .or_insert(id);
        self.sig_srcs.push(SigSrc {
            id,
            module,
            parent,
            span,
            fields,
            appended_fact,
            is_var,
        });
        id
    }

    /// Binds each module instance's parameters to argument sigs
    /// (resolution-doc §2.3): every open edge resolves its argument names in
    /// the *opener's* sig scope and assigns them to the target instance's
    /// param slots. The exact-param-on-var-sig reject (§5.1 last row) fires
    /// here.
    pub(super) fn resolve_params(&mut self) {
        for m in 0..self.graph.modules.len() {
            let opener = ModuleId::from_index(m);
            let edges = self.graph.modules[opener].opens.clone();
            for edge in &edges {
                let target = edge.target;
                let params = self.graph.modules[target].params.clone();
                for (i, binding) in params.iter().enumerate() {
                    let Some(arg) = edge.args.get(i) else {
                        continue;
                    };
                    // Resolve the (single-segment, load-time-grounded) arg name
                    // as a sig visible from the opener.
                    if let Some(sig) = self.lookup_sig_from(opener, &arg.segments) {
                        if binding.is_exact && self.world.sigs[sig].is_var {
                            self.error(ResolveError::ExactParamVarSig { span: edge.span });
                        }
                        self.mods[target.index()]
                            .param_sigs
                            .entry(binding.param.clone())
                            .or_insert(sig);
                    }
                }
            }
        }
    }

    /// Phase 4b: resolves sig parents, detects inheritance cycles, and computes
    /// each sig's type (resolution-doc §3.1). Runs `resolveSig` memoized +
    /// recursive via an explicit topo walk.
    pub(super) fn resolve_sig_hierarchy(&mut self) {
        // `state[i]`: 0 = unvisited, 1 = on-stack (cycle marker), 2 = done.
        let n = self.sig_srcs.len();
        let mut state = vec![0u8; n];
        for i in 0..n {
            self.resolve_one_sig(i, &mut state);
        }
        // Attach fields list onto each sig now that ids are stable (fields are
        // filled in the field pass; here we just carry the count-free vector).
        // var/static warnings (resolution-doc §3.1/§5.2), best-effort.
        for i in 0..n {
            self.emit_var_static_warnings(i);
        }
    }

    fn resolve_one_sig(&mut self, i: usize, state: &mut [u8]) {
        if state[i] == 2 {
            return;
        }
        if state[i] == 1 {
            // Back-edge onto the resolution stack: cyclic inheritance.
            let src = &self.sig_srcs[i];
            self.error(ResolveError::CyclicInheritance {
                name: self.world.sigs[src.id].name.clone(),
                span: src.span,
            });
            return;
        }
        state[i] = 1;

        let module = self.sig_srcs[i].module;
        let id = self.sig_srcs[i].id;
        let kind = match self.parent_of(i) {
            ResolvedParent::Prim(parent) => {
                if let Some(p) = parent {
                    self.resolve_parent_sig(p, state);
                }
                SigKind::Prim { parent }
            }
            ResolvedParent::Subset { parents, exact } => {
                for &p in &parents {
                    self.resolve_parent_sig(p, state);
                }
                SigKind::Subset { parents, exact }
            }
            ResolvedParent::Error => SigKind::Prim {
                parent: Some(self.world.builtins.univ),
            },
        };
        let ty = self.compute_sig_type(id, &kind);
        self.world.sigs[id].kind = kind;
        self.world.sigs[id].ty = ty;
        let _ = module;
        state[i] = 2;
    }

    /// Recurse into a parent sig's own resolution (memoized), so cycles are
    /// caught on the stack.
    fn resolve_parent_sig(&mut self, parent: SigId, state: &mut [u8]) {
        if let Some(idx) = self.sig_srcs.iter().position(|s| s.id == parent) {
            self.resolve_one_sig(idx, state);
        }
    }

    /// Resolves the parent clause of `sig_srcs[i]` to sig ids, emitting the
    /// parent-not-found / extends-subset rejects (resolution-doc §3.1).
    fn parent_of(&mut self, i: usize) -> ResolvedParent {
        let module = self.sig_srcs[i].module;
        match &self.sig_srcs[i].parent {
            ParentSpec::Top => ResolvedParent::Prim(Some(self.world.builtins.univ)),
            ParentSpec::ExtendsSig(p) => ResolvedParent::Prim(Some(*p)),
            ParentSpec::Extends(name) => {
                let segs = seg_texts(name);
                let Some(p) = self.lookup_sig_from(module, &segs) else {
                    self.error(ResolveError::ParentSigNotFound {
                        name: name_str(name),
                        span: name.span,
                    });
                    return ResolvedParent::Error;
                };
                if matches!(self.world.sigs[p].kind, SigKind::Subset { .. }) {
                    self.error(ResolveError::ExtendsSubsetSig {
                        name: name_str(name),
                        span: name.span,
                    });
                    ResolvedParent::Error
                } else {
                    ResolvedParent::Prim(Some(p))
                }
            }
            ParentSpec::Subset { parents, exact } => {
                let exact = *exact;
                let mut ids = Vec::with_capacity(parents.len());
                let parents = parents.clone();
                for name in &parents {
                    let segs = seg_texts(name);
                    match self.lookup_sig_from(module, &segs) {
                        Some(p) => ids.push(p),
                        None => {
                            self.error(ResolveError::ParentSigNotFound {
                                name: name_str(name),
                                span: name.span,
                            });
                        }
                    }
                }
                if ids.is_empty() {
                    ResolvedParent::Error
                } else {
                    ResolvedParent::Subset {
                        parents: ids,
                        exact,
                    }
                }
            }
        }
    }

    /// The unary type a sig denotes: `{self}` for a prim sig, the union of the
    /// parents' types for a subset sig (resolution-doc §4.1).
    fn compute_sig_type(&self, id: SigId, kind: &SigKind) -> Type {
        match kind {
            SigKind::Prim { .. } => Type::unary(id),
            SigKind::Subset { parents, .. } => {
                let mut ty = Type::empty();
                for &p in parents {
                    ty = ty.union(&self.world, &self.world.sigs[p].ty);
                }
                if ty.is_error() {
                    // Degenerate (all parents unresolved): fall back to univ.
                    Type::unary(self.world.builtins.univ)
                } else {
                    ty
                }
            }
        }
    }

    /// Static/variable mismatch warnings (resolution-doc §5.2 E(a)/E(b)/E(c),
    /// `CompModule.resolveSig`). A parent is "variable" iff its own sig is `var`
    /// (`n.isVariable != null`); `univ`/builtins never count.
    fn emit_var_static_warnings(&mut self, i: usize) {
        let src = &self.sig_srcs[i];
        let id = src.id;
        let is_var = src.is_var;
        let span = self.world.sigs[id].span;
        // The reference splits by parent kind: the subset branch only emits
        // E(a) (static under a variable parent); the prim-`extends` branch emits
        // both E(b) (static under variable) and E(c) (redundant `var`). So the
        // redundant-`var` warning is **prim-only** — a `var sig A in B` with a
        // static `B` never warns.
        let (parents, is_subset): (Vec<SigId>, bool) = match &self.world.sigs[id].kind {
            SigKind::Prim { parent: Some(p) } => (vec![*p], false),
            SigKind::Subset { parents, .. } => (parents.clone(), true),
            SigKind::Prim { parent: None } => (Vec::new(), false),
        };
        for p in parents {
            if self.world.sigs[p].is_builtin {
                continue; // `n != UNIV` in the reference.
            }
            let parent_var = self.world.sigs[p].is_var;
            if parent_var && !is_var {
                // E(a)/E(b): static sig under a variable parent (both branches).
                self.warn(ResolveWarning::SigStaticVarParent { span });
            } else if !parent_var && is_var && !is_subset {
                // E(c): variable sig under a static parent — redundant `var`.
                // Prim `extends` only.
                self.warn(ResolveWarning::SigRedundantVar { span });
            }
        }
    }

    /// Looks up a sig by (possibly qualified) name segments, from `module`'s
    /// scope: qualified prefixes walk the open aliases; the tail is searched in
    /// the landing module and its reachable set, plus module params and
    /// builtins (resolution-doc §2.4/§4.4, sig subset).
    pub(super) fn lookup_sig_from(&self, module: ModuleId, raw: &[String]) -> Option<SigId> {
        let segments = super::strip_this(raw.to_vec());
        let segments = &segments[..];
        if segments.is_empty() {
            return None;
        }
        // Builtin names.
        if segments.len() == 1 {
            match segments[0].as_str() {
                "Int" => return Some(self.world.builtins.int),
                "String" => return Some(self.world.builtins.string),
                "univ" => return Some(self.world.builtins.univ),
                "none" => return Some(self.world.builtins.none),
                _ => {}
            }
        }
        // `seq/Int` (SEQIDX) — written two-segment or synthesized single-segment.
        if segments.join("/") == "seq/Int" {
            return Some(self.world.builtins.seq_int);
        }

        // Qualified: walk alias prefix, then look up the tail in that module.
        // A prefix matching no alias is a genuine qualified failure with no
        // unqualified fallback (so `Color/Red` does not find a bare `Red`).
        if segments.len() > 1 {
            let refs: Vec<&str> = segments.iter().map(String::as_str).collect();
            let (landing, consumed) = self.graph.walk_prefix(module, &refs, module);
            if consumed == 0 {
                return None;
            }
            if consumed < segments.len() {
                let tail = &segments[consumed..];
                if tail.len() == 1 {
                    if let Some(&id) = self.mods[landing.index()].sigs.get(&tail[0]) {
                        return Some(id);
                    }
                    if let Some(&id) = self.mods[landing.index()].param_sigs.get(&tail[0]) {
                        return Some(id);
                    }
                }
            }
            return None;
        }

        // Unqualified: search reachable modules for a bare sig / param.
        let bare = &segments[segments.len() - 1];
        for &rm in &self.reachable[module.index()] {
            if let Some(&id) = self.mods[rm.index()].sigs.get(bare) {
                return Some(id);
            }
            if let Some(&id) = self.mods[rm.index()].param_sigs.get(bare) {
                return Some(id);
            }
        }
        None
    }
}

/// The resolved shape of a parent clause.
enum ResolvedParent {
    Prim(Option<SigId>),
    Subset { parents: Vec<SigId>, exact: bool },
    Error,
}

/// `QualName` → owned segment strings.
pub(super) fn seg_texts(name: &QualName) -> Vec<String> {
    name.segments.iter().map(|s| s.text.clone()).collect()
}

/// `QualName` → `/`-joined display string.
pub(super) fn name_str(name: &QualName) -> String {
    name.segments
        .iter()
        .map(|s| s.text.as_str())
        .collect::<Vec<_>>()
        .join("/")
}

/// Unused import guard (keeps `Ast` referenced for doc links).
#[allow(dead_code)]
fn _ast_ref(_: &Ast) {}
