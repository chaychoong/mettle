//! Phase 8 — the `$` metamodel synthesis (resolution-doc §1 phase 8,
//! ADR-0024 + its 2026-08-25 P0 addendum, bead mt-107 P1).
//!
//! When a model names something the reference's `resolveMeta` would mint, the
//! reference builds a *reflection of the model into the model*: an abstract
//! `sig$` with a `one` sig `S$` per user sig, an abstract `field$` with a `one`
//! sig `S$f` per field, four defined relations on every `S$` (`value`, `fields`,
//! `parent`, `subfields`) and one on every `S$f` (`value`), plus the `static$`
//! and `var$` subset sigs that partition them by variability. This pass mints
//! exactly that, in exactly that order.
//!
//! ## What "exactly that order" buys
//! Three orders are load-bearing and all three are reproduced here:
//!
//! 1. **Synthesis order** — module instances in load order, each module's own
//!    sigs in declaration order, `S$` immediately followed by its own `S$f`s.
//!    This is the order `static$`/`var$` list their members in, and the order
//!    the scope phase (P4) will place atoms in.
//! 2. **Field declaration order on each `S$`** — `value, fields, parent,
//!    subfields`, which is the order the reference adds them and the order the
//!    instance-XML writer emits them (jar-verified, mt-107 P0 §M1).
//! 3. **Field arena order** — `value` for every meta sig first (pass 1), then
//!    `fields`/`parent`/`subfields` per `S$` (pass 2). This is what the
//!    ambiguous-name candidate list is ordered by, and it matches the
//!    reference's own per-name grouping (`V$ <: fields`, `W$ <: fields`,
//!    `Z$ <: fields`).
//!
//! ## What this pass deliberately does *not* do
//! This pass is synthesis only. The quantifier ground expansion (`all f:
//! V$.subfields | …` folded over the meta atoms) lives in `resolve/expr.rs`
//! (mt-107 P2, [`crate::choice::MetaExpansion`]); lowering the defined meta
//! relations is P3; atom placement and `meta="yes"` in the XML are P4. Until P3
//! lands, a model that really uses the metamodel resolves fully and then
//! declines at lowering with a typed defer — never a wrong answer.
//!
//! ## Faithfulness notes worth not re-deriving
//! - **The gate is mettle's narrowed one** (`Resolver::compute_meta_gate`,
//!   mt-108), not the reference's bare `seenDollar`. ADR-0024's addendum pins
//!   that as a decision: a stray `$` must not mint a metamodel. It is still
//!   model-wide, exactly as `seenDollar` is — one genuine meta name anywhere in
//!   the world mints the whole metamodel. What it no longer does is excuse
//!   anything: mt-107 P2 retired the accept-lean regime it used to switch on.
//! - **Builtins get no meta sigs.** `resolveMeta` iterates each module's *user*
//!   sig map, so `Int$` / `String$` / `univ$` / `none$` name nothing and the
//!   reference rejects them (mt-107 P0 §M5, cells `m5_09a`–`m5_09d`). Nothing here mints
//!   them, so they take the ordinary unknown-name path.
//! - **`enum` and `util/ordering` mint their own families.** Both desugar to
//!   ordinary sigs before this pass runs, so `Color$`/`Red$`/`Green$` and
//!   `ordering/Ord$`/`Ord$First`/`Ord$Next` appear with no special casing —
//!   including the `ordering` family an `enum` opens behind the user's back
//!   (P0 §M5, cell `m5_05`).
//! - **The reference's var-inheritance is inconsistent and both halves are
//!   copied** (P0 SURPRISE 6): `S$f` is bucketed into `static$`/`var$` by the
//!   *field's* own variability, while the `value` it declares takes the
//!   *sig's*. `sig B { var s: … }` therefore lands `B$s` in `var$` with a
//!   non-`var` `B$s.value`.
//! - **Meta names are body-only.** This pass runs after every declaration phase
//!   (4–7), so a meta name in a field bound, a func signature or a pred
//!   parameter resolves against a world that does not contain it yet — which is
//!   exactly the reference's own phase-order reject (P0 SURPRISE 5).

use als_syntax::ast::{ExprId, SigMult};
use als_syntax::ArenaId;

use crate::graph::ModuleId;
use crate::ty::Type;
use crate::world::{MetaDef, MetaEmptyFact, MetaModel, ResolvedField, ResolvedSig, SigId, SigKind};

use super::Resolver;

/// The four defined relations of an `S$`, in the reference's declaration order
/// (`resolveMeta` `:2170`, `:2191`, `:2207`, `:2228`) — which is also the order
/// the instance-XML writer emits them in. An `S$f` declares only `RELATIONS[0]`.
const RELATIONS: [&str; 4] = ["value", "fields", "parent", "subfields"];

/// What pass 1 leaves for pass 2 and for the `static$` / `var$` split.
struct Minted {
    /// Every meta sig in synthesis order, `S$` and `S$f` interleaved, paired
    /// with the variability that buckets it (the **sig's** for an `S$`, the
    /// **field's** for an `S$f` — P0 SURPRISE 6).
    atoms: Vec<(SigId, bool)>,
    /// The `S$` family alone, same order — the jar's `metaSigAtoms`.
    sig_atoms: Vec<SigId>,
    /// The `S$f` family alone, same order — the jar's `metaFieldAtoms`.
    field_atoms: Vec<SigId>,
    /// User sig → its meta sig, `SigId`-indexed.
    meta_of: Vec<Option<SigId>>,
    /// User sig → the meta sigs of the fields it declares itself, in
    /// declaration order, `SigId`-indexed.
    own_meta_fields: Vec<Vec<SigId>>,
}

impl Minted {
    /// The meta sigs whose variability is `is_var`, in synthesis order — the
    /// membership list of `var$` (`true`) or `static$` (`false`).
    fn bucket(&self, is_var: bool) -> Vec<SigId> {
        self.atoms
            .iter()
            .filter(|&&(_, v)| v == is_var)
            .map(|&(id, _)| id)
            .collect()
    }
}

impl Resolver<'_> {
    /// Phase 8: mints the `$` metamodel when the mt-108 meta gate fired.
    ///
    /// A no-op — not even an allocation — for every model without a genuine
    /// meta name, which is what keeps the rest of the corpus byte-identical.
    pub(super) fn synthesize_meta(&mut self) {
        if !self.meta_gate {
            return;
        }
        let root = self.graph.root;
        let univ = self.world.builtins.univ;

        // The reflection targets, in the reference's iteration order: every
        // loaded module instance in load order, each module's own sig map in
        // declaration order (`m.sigs`, a `LinkedHashMap`; mettle's `IndexMap`
        // has the same contract). Snapshotted **first**, because minting
        // appends to the very tables being read — and the metamodel does not
        // reflect itself: no dump anywhere in the P0 wave carries a `sig$$`.
        let targets = self.meta_targets();

        // `sig$` and `field$`: abstract, top-level, in the root module. The
        // reference registers them as macros rather than builtins (`:2239-2240`);
        // mettle registers them as root-module sigs, which is the same name
        // surface — they are reachable unqualified from every module, and a
        // declared `$` name is a parse-time reject so nothing can shadow them.
        let sig_meta = self.alloc_meta_sig(root, "sig$".to_owned(), univ, true, None, false);
        let field_meta = self.alloc_meta_sig(root, "field$".to_owned(), univ, true, None, false);
        let minted = self.mint_meta_sigs(&targets, sig_meta, field_meta);
        self.mint_meta_relations(&targets, &minted);

        // `static$` / `var$`: subset sigs over the meta sigs, partitioned by
        // variability, **exact** when non-empty (`:2193-2198`). When a bucket is
        // empty the reference falls back to a non-exact subset of `univ` plus an
        // emptiness fact, which is why `var$` reads `SUBSET([univ])` in every
        // static model's dump.
        let statics = minted.bucket(false);
        let vars = minted.bucket(true);
        let static_meta = self.alloc_meta_subset(root, "static$", &statics);
        let var_meta = self.alloc_meta_subset(root, "var$", &vars);

        // Emptiness facts (`:2230-2237`). `sig$` is empty exactly when the model
        // declares no sig at all — reachable, since `run { no sig$ }` fires the
        // gate on the reserved name alone.
        //
        // Deliberately NOT invented: a `field$` emptiness fact. The memo's
        // source reading names three facts and P0 probed no fields-free `$`
        // model, so a model with sigs but no fields leaves `field$` childless
        // here exactly as the reference leaves it. If P4's bounds work shows a
        // divergence it is one probe cell away; guessing a fourth fact would
        // constrain a sig the reference may leave free.
        let mut empty_facts = Vec::new();
        if minted.sig_atoms.is_empty() {
            empty_facts.push(MetaEmptyFact {
                name: "sig$fact".to_owned(),
                sig: sig_meta,
            });
        }
        if statics.is_empty() {
            empty_facts.push(MetaEmptyFact {
                name: "static$fact".to_owned(),
                sig: static_meta,
            });
        }
        if vars.is_empty() {
            empty_facts.push(MetaEmptyFact {
                name: "var$fact".to_owned(),
                sig: var_meta,
            });
        }

        self.world.meta = Some(MetaModel {
            sig_meta,
            field_meta,
            static_meta,
            var_meta,
            sig_atoms: minted.sig_atoms,
            field_atoms: minted.field_atoms,
            atoms: minted.atoms.into_iter().map(|(id, _)| id).collect(),
            empty_facts,
        });

        // The minted sigs need their global labels (`this/V$`, `ao/Ord$`) — the
        // additive second run the design memo called for. Idempotent for the
        // user sigs it recomputes.
        self.compute_qualified_names();
    }

    /// Pass 1 — mints `S$` and its own `S$f`s interleaved, each carrying its
    /// `value` relation, in the reference's synthesis order.
    ///
    /// Returns everything pass 2 and the subset sigs need — see [`Minted`].
    fn mint_meta_sigs(
        &mut self,
        targets: &[(ModuleId, SigId)],
        sig_meta: SigId,
        field_meta: SigId,
    ) -> Minted {
        let mut sig_atoms: Vec<SigId> = Vec::new();
        let mut field_atoms: Vec<SigId> = Vec::new();
        let mut atoms: Vec<(SigId, bool)> = Vec::new();
        // Per user sig: its meta sig, and the meta sigs of the fields it
        // declares itself. Indexed by `SigId`, so deterministic by construction
        // (STYLE D2 — no hashing anywhere near an order that matters).
        let mut meta_of: Vec<Option<SigId>> = vec![None; self.world.sigs.len()];
        let mut own_meta_fields: Vec<Vec<SigId>> = vec![Vec::new(); self.world.sigs.len()];

        for &(module, sig) in targets {
            let label = self.world.sigs[sig].name.clone();
            let sig_private = self.world.sigs[sig].is_private;
            let sig_var = self.world.sigs[sig].is_var;

            let s_meta = self.alloc_meta_sig(
                module,
                format!("{label}$"),
                sig_meta,
                false,
                Some(SigMult::One),
                sig_private,
            );
            meta_of[sig.index()] = Some(s_meta);
            sig_atoms.push(s_meta);
            atoms.push((s_meta, sig_var));

            // `S$ <: value = S` — the sig itself (`:2170`).
            let ty = Type::unary(s_meta).product(&self.world, &self.world.sigs[sig].ty);
            self.alloc_meta_field(
                s_meta,
                RELATIONS[0],
                ty,
                sig_var,
                sig_private,
                MetaDef::Sig(sig),
            );

            for field in self.world.sigs[sig].fields.clone() {
                let f_label = self.world.fields[field].name.clone();
                let f_private = sig_private || self.world.fields[field].is_private;
                let f_var = self.world.fields[field].is_var;
                let f_meta = self.alloc_meta_sig(
                    module,
                    format!("{label}${f_label}"),
                    field_meta,
                    false,
                    Some(SigMult::One),
                    f_private,
                );
                field_atoms.push(f_meta);
                // SURPRISE 6, half one: the bucketing reads the FIELD's `var`.
                atoms.push((f_meta, f_var));
                own_meta_fields[sig.index()].push(f_meta);

                // `S$f <: value = f` — the field relation itself (`:2185`).
                let ty = Type::unary(f_meta).product(&self.world, &self.world.fields[field].ty);
                // SURPRISE 6, half two: the declaration reads the SIG's `var`,
                // so a `var` field of a static sig gets a static `value` over a
                // mutable relation. The reference's inconsistency, copied.
                self.alloc_meta_field(
                    f_meta,
                    RELATIONS[0],
                    ty,
                    sig_var,
                    f_private,
                    MetaDef::Field(field),
                );
            }
        }

        Minted {
            atoms,
            sig_atoms,
            field_atoms,
            meta_of,
            own_meta_fields,
        }
    }

    /// Pass 2 — `fields`, `parent`, `subfields` on every `S$`. A second pass
    /// because `parent` may name a forward-declared sig's meta sig and
    /// `subfields` needs every descendant's, so neither is knowable during
    /// pass 1.
    fn mint_meta_relations(&mut self, targets: &[(ModuleId, SigId)], minted: &Minted) {
        for &(_, sig) in targets {
            let Some(s_meta) = minted.meta_of[sig.index()] else {
                continue;
            };
            let private = self.world.sigs[s_meta].is_private;

            // `fields` — the sig's own meta-field sigs (`:2191`).
            let own = minted.own_meta_fields[sig.index()].clone();
            self.alloc_meta_union_field(s_meta, RELATIONS[1], own.clone(), private);

            // `parent` — the parent's meta sig, else `none` (`:2199-2207`).
            // Only a prim `extends` parent counts: a subset sig has no
            // `PrimSig.parent`, and a builtin (`univ`) has no meta sig.
            let parent = match self.world.sigs[sig].kind {
                SigKind::Prim { parent: Some(p) } => {
                    minted.meta_of.get(p.index()).copied().flatten()
                }
                SigKind::Prim { parent: None } | SigKind::Subset { .. } => None,
            };
            self.alloc_meta_union_field(
                s_meta,
                RELATIONS[2],
                parent.into_iter().collect(),
                private,
            );

            // `subfields` — own meta-field sigs plus every descendant sig's,
            // descendants in synthesis order (`:2208-2228`).
            let mut sub = own;
            for &(_, other) in targets {
                if other != sig && self.world.is_same_or_descendent(other, sig) {
                    sub.extend_from_slice(&minted.own_meta_fields[other.index()]);
                }
            }
            self.alloc_meta_union_field(s_meta, RELATIONS[3], sub, private);
        }
    }

    /// The user sigs to reflect, in the reference's `resolveMeta` iteration
    /// order: module instances in load order (root first), each module's own sig
    /// map in declaration order.
    ///
    /// A module *parameter* is not a target: it is bound to an argument sig
    /// declared elsewhere, and the reference names meta sigs after the argument
    /// sig's own label — so `elem$` denotes nothing even inside
    /// `util/ordering[elem]` (the same rule mt-108's gate already encodes). A
    /// **root** module's own header params are different: mettle materializes
    /// them as real top-level sigs in the root's sig map, so they reflect like
    /// any other sig.
    fn meta_targets(&self) -> Vec<(ModuleId, SigId)> {
        let mut out = Vec::new();
        for m in 0..self.graph.modules.len() {
            let module = ModuleId::from_index(m);
            for (_, &sig) in &self.mods[m].sigs {
                // Defensive, and a statement of intent: the metamodel never
                // reflects itself, however this is called.
                if !self.world.sigs[sig].is_meta {
                    out.push((module, sig));
                }
            }
        }
        out
    }

    /// Allocates one synthesized prim meta sig under `parent` and registers its
    /// label in `module`'s sig table, so ordinary name resolution finds it.
    fn alloc_meta_sig(
        &mut self,
        module: ModuleId,
        name: String,
        parent: SigId,
        is_abstract: bool,
        mult: Option<SigMult>,
        is_private: bool,
    ) -> SigId {
        let id = SigId::from_index(self.world.sigs.len());
        self.world.sigs.alloc(ResolvedSig {
            name: name.clone(),
            // `compute_qualified_names` fills the alias path at the end of the
            // pass, exactly as it does for user sigs.
            qualified_name: name.clone(),
            module,
            span: crate::load::synthetic_span(),
            kind: SigKind::Prim {
                parent: Some(parent),
            },
            is_abstract,
            is_enum: false,
            is_var: false,
            is_private,
            is_builtin: false,
            is_meta: true,
            mult,
            fields: Vec::new(),
            field_disj_groups: Vec::new(),
            appended_fact: None,
            ty: Type::unary(id),
        });
        self.mods[module.index()].sigs.entry(name).or_insert(id);
        id
    }

    /// Allocates one synthesized subset meta sig (`static$` / `var$`) over
    /// `members`, exact when non-empty. An empty bucket becomes a non-exact
    /// subset of `univ`, matching the reference's `SUBSET([univ])` shape.
    fn alloc_meta_subset(&mut self, module: ModuleId, name: &str, members: &[SigId]) -> SigId {
        let (parents, exact) = if members.is_empty() {
            (vec![self.world.builtins.univ], false)
        } else {
            (members.to_vec(), true)
        };
        let mut ty = Type::empty();
        for &p in &parents {
            ty = ty.union(&self.world, &self.world.sigs[p].ty);
        }
        let id = SigId::from_index(self.world.sigs.len());
        self.world.sigs.alloc(ResolvedSig {
            name: name.to_owned(),
            qualified_name: name.to_owned(),
            module,
            span: crate::load::synthetic_span(),
            kind: SigKind::Subset { parents, exact },
            is_abstract: false,
            is_enum: false,
            is_var: false,
            is_private: false,
            is_builtin: false,
            is_meta: true,
            mult: None,
            fields: Vec::new(),
            field_disj_groups: Vec::new(),
            appended_fact: None,
            ty,
        });
        self.mods[module.index()]
            .sigs
            .entry(name.to_owned())
            .or_insert(id);
        id
    }

    /// Allocates one synthesized defined field on a meta sig.
    fn alloc_meta_field(
        &mut self,
        owner: SigId,
        name: &str,
        ty: Type,
        is_var: bool,
        is_private: bool,
        def: MetaDef,
    ) {
        let id = self.world.fields.alloc(ResolvedField {
            name: name.to_owned(),
            owner,
            span: crate::load::synthetic_span(),
            ty,
            is_var,
            is_private,
            is_defined: true,
            is_bound_disj: false,
            // No source AST to point at; `meta_def` is the authority. See the
            // field's own docs — every consumer must branch on `meta_def` first.
            bound: ExprId::from_index(0),
            is_meta: true,
            meta_def: Some(def),
        });
        self.world.sigs[owner].fields.push(id);
    }

    /// Allocates one of the three meta relations whose value is a union of meta
    /// sigs (`fields`, `parent`, `subfields`).
    ///
    /// An empty union types as `{owner -> univ}`, not `{owner -> none}`: the
    /// reference's `ExprConstant.EMPTYNESS` carries a `univ` right column, and
    /// the difference is observable — `Z$ in V$.parent` is a well-typed UNSAT
    /// against a `univ` column and a type-disjoint comparison against a `none`
    /// one (jar-verified, cell `m1_31`).
    fn alloc_meta_union_field(
        &mut self,
        owner: SigId,
        name: &str,
        members: Vec<SigId>,
        is_private: bool,
    ) {
        let ty = if members.is_empty() {
            Type::product_of(vec![owner, self.world.builtins.univ])
        } else {
            let mut ty = Type::empty();
            for &m in &members {
                ty = ty.union(&self.world, &Type::product_of(vec![owner, m]));
            }
            ty
        };
        // Never `var`: these relate meta atoms, which are immutable singletons.
        self.alloc_meta_field(
            owner,
            name,
            ty,
            false,
            is_private,
            MetaDef::MetaSigs(members),
        );
    }
}
