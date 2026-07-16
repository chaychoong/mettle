//! Member registration and resolution: funcs/preds, fields, facts, asserts,
//! macros, and commands (resolution-doc §3.3–§3.7, phases 5/6/7/10/11).

use als_syntax::ast::{
    Ast, CmdTarget, Decl, DeclId, ExprId, ExprKind, FunDecl, Para, ParaId, ParaName, PredDecl,
    ScopeTarget, UnOp,
};
use als_syntax::{ArenaId, Span};

use crate::error::ResolveError;
use crate::graph::ModuleId;
use crate::ty::Type;
use crate::world::{
    FuncId, MacroId, Param, ResolvedCommand, ResolvedField, ResolvedFunc, ResolvedMacro, SigId,
};

use super::expr::Cx;
use super::Resolver;

impl Resolver<'_> {
    /// Registers func/pred, assert, and macro **names** before bodies
    /// (resolution-doc §3.5/§3.6/§3.7): funcs/preds overload; asserts and
    /// macros reject dups; facts are unnamed.
    pub(super) fn register_members(&mut self) {
        for m in 0..self.graph.modules.len() {
            let module = ModuleId::from_index(m);
            let ast = self.ast(module);
            for &para_id in &ast.paragraphs {
                match &ast.paras[para_id] {
                    Para::Pred(p) => {
                        self.register_func(module, para_id, &p.name.text, true, p.is_private);
                    }
                    Para::Fun(f) => {
                        self.register_func(module, para_id, &f.name.text, false, f.is_private);
                    }
                    Para::Assert(a) => self.register_assert(module, a.name.as_ref(), a.span),
                    Para::Macro(mac) => self.register_macro(module, para_id, mac),
                    _ => {}
                }
            }
        }
    }

    fn register_func(
        &mut self,
        module: ModuleId,
        para: ParaId,
        name: &str,
        is_pred: bool,
        is_private: bool,
    ) {
        let span = para_span(&self.ast(module).paras[para]);
        let id = FuncId::from_index(self.world.funcs.len());
        self.world.funcs.alloc(ResolvedFunc {
            name: name.to_owned(),
            module,
            span,
            is_pred,
            is_private,
            params: Vec::new(),
            return_ty: Type::formula(),
            return_decl: None,
        });
        self.mods[module.index()]
            .funcs
            .entry(name.to_owned())
            .or_default()
            .push(id);
        self.func_srcs.push((id, module, para));
    }

    fn register_assert(&mut self, module: ModuleId, name: Option<&ParaName>, span: Span) {
        // Only identifier-named asserts are `check`-able and dup-checked; a
        // string-named assert can never be referenced (resolution-doc §3.6).
        if let Some(ParaName::Ident(id)) = name {
            if self.mods[module.index()].asserts.contains_key(&id.text) {
                self.error(ResolveError::DuplicateAssert {
                    name: id.text.clone(),
                    span: id.span,
                });
            } else {
                self.mods[module.index()]
                    .asserts
                    .insert(id.text.clone(), id.span);
            }
        }
        let _ = span;
    }

    fn register_macro(&mut self, module: ModuleId, para: ParaId, mac: &als_syntax::ast::MacroDecl) {
        if self.mods[module.index()]
            .macros
            .contains_key(&mac.name.text)
        {
            self.error(ResolveError::DuplicateMacro {
                name: mac.name.text.clone(),
                span: mac.name.span,
            });
            return;
        }
        let id = MacroId::from_index(self.world.macros.len());
        self.world.macros.alloc(ResolvedMacro {
            name: mac.name.text.clone(),
            module,
            span: mac.name.span,
            params: mac.params.iter().map(|p| p.text.clone()).collect(),
            body: mac.body,
            is_private: mac.is_private,
        });
        self.mods[module.index()]
            .macros
            .insert(mac.name.text.clone(), id);
        let _ = para;
    }

    // ---- fields (phases 5/7) ----

    /// Resolves the fields matching `defined` (`false` = non-defined bounds,
    /// `true` = `=` defined fields), computing each field's type and rejecting
    /// dup labels / call-in-bound / empty bounds (resolution-doc §3.4).
    pub(super) fn resolve_fields(&mut self, defined: bool) {
        for si in 0..self.sig_srcs.len() {
            let sig = self.sig_srcs[si].id;
            let module = self.sig_srcs[si].module;
            let field_decls = self.sig_srcs[si].fields.clone();
            for d in field_decls {
                let decl = self.ast(module).decls[d].clone();
                let is_def = is_defined_bound(self.ast(module), &decl);
                if is_def != defined {
                    continue;
                }
                self.resolve_one_field(sig, module, &decl, is_def);
            }
        }
    }

    fn resolve_one_field(&mut self, sig: SigId, module: ModuleId, decl: &Decl, defined: bool) {
        // Type the bound in a sig context (implicit `this`), calls disallowed
        // for non-defined bounds (resolution-doc §3.4).
        let field_name = decl
            .names
            .first()
            .map(|n| n.text.clone())
            .unwrap_or_default();
        let (bound_ty, errs, warns) = {
            let mut cx = Cx::new(self, module);
            cx.rootsig = Some(sig);
            cx.no_calls = !defined;
            cx.field_name.clone_from(&field_name);
            cx.env
                .push(("this".to_owned(), self.world.sigs[sig].ty.clone()));
            let t = cx.run_bound(decl.bound);
            (t, cx.errors, cx.warnings)
        };
        self.errors.extend(errs);
        self.warnings.extend(warns);

        // Empty-bound reject (all-`none` relation).
        let none = self.world.builtins.none;
        if bound_ty.has_entries()
            && bound_ty
                .entries
                .iter()
                .all(|p| p.0.iter().all(|&s| s == none))
        {
            self.error(ResolveError::FieldBoundEmpty {
                name: field_name.clone(),
                span: decl.span,
            });
        }

        let owner_ty = self.world.sigs[sig].ty.clone();
        let field_ty = owner_ty.product(&self.world, &bound_ty);
        for name in &decl.names {
            // Duplicate label within this sig.
            if self.world.sigs[sig]
                .fields
                .iter()
                .any(|&f| self.world.fields[f].name == name.text)
            {
                self.error(ResolveError::DuplicateField {
                    name: name.text.clone(),
                    span: name.span,
                });
                continue;
            }
            let fid = self.world.fields.alloc(ResolvedField {
                name: name.text.clone(),
                owner: sig,
                span: name.span,
                ty: field_ty.clone(),
                is_var: decl.is_var,
                is_private: decl.is_private,
                is_defined: defined,
            });
            self.world.sigs[sig].fields.push(fid);
        }
    }

    /// Field-name clash across overlapping sigs (`rejectNameClash`, phase 9,
    /// resolution-doc §3.4, probe 06): two fields with the same label whose
    /// owners' first columns overlap.
    pub(super) fn reject_name_clash(&mut self) {
        let n = self.world.fields.len();
        let mut clashes: Vec<(String, Span)> = Vec::new();
        for i in 0..n {
            for j in (i + 1)..n {
                let fi = FuncIdless(i);
                let fj = FuncIdless(j);
                let (a, b) = (
                    crate::world::FieldId::from_index(fi.0),
                    crate::world::FieldId::from_index(fj.0),
                );
                let (na, nb) = (&self.world.fields[a], &self.world.fields[b]);
                if na.name != nb.name {
                    continue;
                }
                let oa = na.owner;
                let ob = nb.owner;
                // Same sig is caught by the dup-in-sig check; only cross-sig
                // overlaps concern us here.
                if oa == ob {
                    continue;
                }
                if self.world.is_same_or_descendent(oa, ob)
                    || self.world.is_same_or_descendent(ob, oa)
                {
                    clashes.push((nb.name.clone(), nb.span));
                }
            }
        }
        for (name, span) in clashes {
            self.error(ResolveError::FieldNameClash { name, span });
        }
    }

    // ---- func/pred decls (phase 6) ----

    /// Resolves func/pred params + return types (resolution-doc §3.5): params
    /// left-to-right (no calls), dup-name reject, receiver → `this` param.
    pub(super) fn resolve_func_decls(&mut self) {
        for k in 0..self.func_srcs.len() {
            let (fid, module, para) = self.func_srcs[k];
            let (params, return_ty, errs, warns) = self.resolve_one_func_decl(fid, module, para);
            self.errors.extend(errs);
            self.warnings.extend(warns);
            self.world.funcs[fid].params = params;
            self.world.funcs[fid].return_ty = return_ty;
            // Capture the return-decl expr for per-call specialization.
            if let Para::Fun(f) = &self.ast(module).paras[para] {
                self.world.funcs[fid].return_decl = Some(f.returns);
            }
        }
    }

    fn resolve_one_func_decl(
        &self,
        fid: FuncId,
        module: ModuleId,
        para: ParaId,
    ) -> (
        Vec<Param>,
        Type,
        Vec<ResolveError>,
        Vec<ResolveWarningAlias>,
    ) {
        let ast = self.ast(module);
        let is_pred = self.world.funcs[fid].is_pred;
        let (receiver, param_decls, returns) = match &ast.paras[para] {
            Para::Pred(p) => (p.receiver.as_ref(), &p.params, None),
            Para::Fun(f) => (f.receiver.as_ref(), &f.params, Some(f.returns)),
            _ => return (Vec::new(), Type::formula(), Vec::new(), Vec::new()),
        };
        let mut cx = Cx::new(self, module);
        cx.no_calls = true; // rootfunparam: params cannot call funcs/preds
        let mut params: Vec<Param> = Vec::new();
        let mut seen: Vec<String> = Vec::new();

        if let Some(recv) = receiver {
            let segs: Vec<String> = recv.segments.iter().map(|s| s.text.clone()).collect();
            let ty = self
                .lookup_sig_from(module, &segs)
                .map_or_else(Type::empty, |s| self.world.sigs[s].ty.clone());
            cx.env.push(("this".to_owned(), ty.clone()));
            params.push(Param {
                name: "this".to_owned(),
                ty,
            });
            seen.push("this".to_owned());
        }

        for &d in param_decls {
            let decl = ast.decls[d].clone();
            let ty = cx.run_bound(decl.bound);
            for name in &decl.names {
                if seen.contains(&name.text) {
                    cx.errors.push(ResolveError::DuplicateParam {
                        name: name.text.clone(),
                        span: name.span,
                    });
                }
                seen.push(name.text.clone());
                cx.env.push((name.text.clone(), ty.clone()));
                params.push(Param {
                    name: name.text.clone(),
                    ty: ty.clone(),
                });
            }
        }

        let return_ty = if is_pred {
            Type::formula()
        } else if let Some(ret) = returns {
            cx.run_bound(ret)
        } else {
            Type::formula()
        };
        (params, return_ty, cx.errors, cx.warnings)
    }

    // ---- bodies (phase 10) ----

    /// Resolves func/pred bodies, sig + free facts, and asserts
    /// (resolution-doc §3.3/§3.5/§3.6). Fun body arity must equal the declared
    /// return arity (probe 35).
    pub(super) fn resolve_bodies(&mut self) {
        // Func/pred bodies.
        for k in 0..self.func_srcs.len() {
            let (fid, module, para) = self.func_srcs[k];
            let (errs, warns) = self.resolve_func_body(fid, module, para);
            self.errors.extend(errs);
            self.warnings.extend(warns);
        }

        // Facts (free + sig-appended) and asserts, per module in order.
        for m in 0..self.graph.modules.len() {
            let module = ModuleId::from_index(m);
            let ast = self.ast(module);
            for &para_id in &ast.paragraphs {
                match &ast.paras[para_id] {
                    Para::Fact(f) => self.resolve_formula(module, None, f.body),
                    Para::Assert(a) => self.resolve_formula(module, None, a.body),
                    _ => {}
                }
            }
        }
        // Sig-appended facts (implicit `this`).
        for si in 0..self.sig_srcs.len() {
            if let Some(body) = self.sig_srcs[si].appended_fact {
                let sig = self.sig_srcs[si].id;
                let module = self.sig_srcs[si].module;
                self.resolve_formula(module, Some(sig), body);
            }
        }
    }

    fn resolve_func_body(
        &self,
        fid: FuncId,
        module: ModuleId,
        para: ParaId,
    ) -> (Vec<ResolveError>, Vec<ResolveWarningAlias>) {
        let ast = self.ast(module);
        let is_pred = self.world.funcs[fid].is_pred;
        let body = match &ast.paras[para] {
            Para::Pred(p) => p.body,
            Para::Fun(f) => f.body,
            _ => return (Vec::new(), Vec::new()),
        };
        let mut cx = Cx::new(self, module);
        for p in &self.world.funcs[fid].params {
            cx.env.push((p.name.clone(), p.ty.clone()));
        }
        if is_pred {
            cx.run_formula(body);
        } else {
            let bt = cx.run_set(body);
            let ret = &self.world.funcs[fid].return_ty;
            // Body arity must match the declared return arity (`Func.setBody`).
            if !bt.is_error() && !ret.is_error() && ret.has_entries() && !bt.has_common_arity(ret) {
                cx.errors.push(ResolveError::FuncBodyArity {
                    name: self.world.funcs[fid].name.clone(),
                    span: para_span(&ast.paras[para]),
                });
            }
        }
        (cx.errors, cx.warnings)
    }

    /// Types a formula body (fact/assert/appended fact) and drains diagnostics.
    fn resolve_formula(&mut self, module: ModuleId, rootsig: Option<SigId>, body: ExprId) {
        let (errs, warns) = {
            let mut cx = Cx::new(self, module);
            cx.rootsig = rootsig;
            if let Some(s) = rootsig {
                cx.env
                    .push(("this".to_owned(), self.world.sigs[s].ty.clone()));
            }
            cx.run_formula(body);
            (cx.errors, cx.warnings)
        };
        self.errors.extend(errs);
        self.warnings.extend(warns);
    }

    // ---- commands (phase 11) ----

    /// Resolves commands: targets (pred/fun for `run`, assert for `check`,
    /// anonymous blocks) and scopes (resolution-doc §3.6).
    pub(super) fn resolve_commands(&mut self) {
        for m in 0..self.graph.modules.len() {
            let module = ModuleId::from_index(m);
            let ast = self.ast(module);
            let cmds: Vec<ParaId> = ast
                .paragraphs
                .iter()
                .copied()
                .filter(|&p| matches!(ast.paras[p], Para::Cmd(_)))
                .collect();
            for para in cmds {
                self.resolve_one_command(module, para);
            }
        }
    }

    fn resolve_one_command(&mut self, module: ModuleId, para: ParaId) {
        let ast = self.ast(module);
        let Para::Cmd(cmd) = &ast.paras[para] else {
            return;
        };
        let kind = cmd.kind;
        let span = cmd.span;
        let is_check = matches!(kind, als_syntax::ast::CmdKind::Check);

        match &cmd.target {
            CmdTarget::Name(qn) => {
                let segs: Vec<String> = qn.segments.iter().map(|s| s.text.clone()).collect();
                let found = if is_check {
                    self.lookup_assert(module, &segs)
                } else {
                    !self.lookup_run_target(module, &segs).is_empty()
                };
                if !found {
                    self.error(ResolveError::CommandTargetNotFound {
                        name: segs.join("/"),
                        span,
                    });
                }
            }
            CmdTarget::Block(body) => {
                self.resolve_formula(module, None, *body);
            }
        }

        // Scopes.
        if let Some(scope) = &cmd.scope {
            let entries = scope.entries.clone();
            for entry in &entries {
                if let ScopeTarget::Sig(qn) = &entry.target {
                    let segs: Vec<String> = qn.segments.iter().map(|s| s.text.clone()).collect();
                    match self.lookup_sig_from(module, &segs) {
                        None => self.error(ResolveError::ScopeSigNotFound {
                            name: segs.join("/"),
                            span: entry.span,
                        }),
                        Some(sig) => self.check_scope_sig(sig, entry.is_exact, entry.span, &segs),
                    }
                }
            }
        }

        self.world.commands.push(ResolvedCommand { span, kind });
    }

    fn check_scope_sig(&mut self, sig: SigId, is_exact: bool, span: Span, segs: &[String]) {
        let is_var = self.world.sigs[sig].is_var;
        if is_var {
            if is_exact {
                self.error(ResolveError::ExactScopeOnVar {
                    name: segs.join("/"),
                    span,
                });
            }
            // Non-top-level = parent is not univ.
            let top_level = matches!(
                self.world.sigs[sig].kind,
                crate::world::SigKind::Prim { parent: Some(p) } if p == self.world.builtins.univ
            );
            if !top_level {
                self.error(ResolveError::MutableSigScoped {
                    name: segs.join("/"),
                    span,
                });
            }
        }
    }

    /// A `check` target: a reachable assertion by (qualified) name.
    fn lookup_assert(&self, module: ModuleId, segs: &[String]) -> bool {
        if segs.len() > 1 {
            let refs: Vec<&str> = segs.iter().map(String::as_str).collect();
            let (landing, consumed) = self.graph.walk_prefix(module, &refs, module);
            // A qualified name whose prefix matched no alias does not fall back
            // to an unqualified search (mirrors the sig/func lookups).
            if consumed == 0 {
                return false;
            }
            if consumed < segs.len() {
                let tail = &segs[consumed..];
                return tail.len() == 1
                    && self.mods[landing.index()].asserts.contains_key(&tail[0]);
            }
            return false;
        }
        let bare = &segs[segs.len() - 1];
        self.reachable[module.index()]
            .iter()
            .any(|&rm| self.mods[rm.index()].asserts.contains_key(bare))
    }

    /// A `run` target: reachable funcs/preds by (qualified) name.
    fn lookup_run_target(&self, module: ModuleId, segs: &[String]) -> Vec<FuncId> {
        let mut out = Vec::new();
        if segs.len() > 1 {
            let refs: Vec<&str> = segs.iter().map(String::as_str).collect();
            let (landing, consumed) = self.graph.walk_prefix(module, &refs, module);
            if consumed == 0 {
                return out;
            }
            if consumed < segs.len() {
                let tail = &segs[consumed..];
                if tail.len() == 1 {
                    if let Some(v) = self.mods[landing.index()].funcs.get(&tail[0]) {
                        out.extend_from_slice(v);
                    }
                }
            }
            return out;
        }
        let bare = &segs[segs.len() - 1];
        for &rm in &self.reachable[module.index()] {
            if let Some(v) = self.mods[rm.index()].funcs.get(bare) {
                out.extend_from_slice(v);
            }
        }
        out
    }
}

/// Alias so members.rs signatures read clearly; the resolver's warning type.
type ResolveWarningAlias = crate::warning::ResolveWarning;

/// A tiny index wrapper used to build `FieldId`s in the clash pass without
/// re-borrowing conventions (keeps the double loop legible).
struct FuncIdless(usize);

/// The span of any paragraph (each variant carries one).
fn para_span(para: &Para) -> Span {
    match para {
        Para::Sig(s) => s.span,
        Para::Enum(e) => e.span,
        Para::Fact(f) => f.span,
        Para::Pred(p) => p.span,
        Para::Fun(f) => f.span,
        Para::Assert(a) => a.span,
        Para::Macro(m) => m.span,
        Para::Cmd(c) => c.span,
    }
}

/// Whether a decl's bound is a defined (`=`) field marker (`UnOp::ExactlyOf`).
fn is_defined_bound(ast: &Ast, decl: &Decl) -> bool {
    matches!(
        &ast.exprs[decl.bound].kind,
        ExprKind::Unary {
            op: UnOp::ExactlyOf,
            ..
        }
    )
}

/// Keeps the `FunDecl`/`PredDecl`/`DeclId` imports referenced for doc links.
#[allow(dead_code)]
fn _touch(_: &FunDecl, _: &PredDecl, _: DeclId) {}
