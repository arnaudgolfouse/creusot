use super::pearlite::{normalize, pearlite_stub, Literal, Stub, Term, TermKind};
use crate::{
    ctx::*,
    error::{Error, InternalError},
    util::{self, is_spec},
};
use rustc_ast::{
    ast::{AttrArgs, AttrArgsEq},
    AttrItem,
};
use rustc_hir::def_id::DefId;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{Body, Local, SourceInfo, SourceScope, OUTERMOST_SOURCE_SCOPE},
    thir::{self, ClosureExpr, ExprKind, Thir},
    ty::{self, EarlyBinder, GenericArgs, GenericArgsRef, ParamEnv, TyCtxt},
};
use rustc_span::Symbol;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, Default, TypeFoldable, TypeVisitable)]
pub struct PreContract<'tcx> {
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) requires: Vec<Term<'tcx>>,
    pub(crate) ensures: Vec<Term<'tcx>>,
    pub(crate) no_panic: bool,
    pub(crate) terminates: bool,
    pub(crate) extern_no_spec: bool,
}

impl<'tcx> PreContract<'tcx> {
    pub(crate) fn subst(&mut self, subst: &HashMap<Symbol, Term<'tcx>>) {
        for term in self.terms_mut() {
            term.subst(subst);
        }
    }

    pub(crate) fn normalize(mut self, tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>) -> Self {
        for term in self.terms_mut() {
            normalize(tcx, param_env, term);
        }
        self
    }

    pub(crate) fn is_requires_false(&self) -> bool {
        self.requires.iter().any(|req| matches!(req.kind, TermKind::Lit(Literal::Bool(false))))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty() && self.variant.is_none()
    }

    #[allow(dead_code)]
    pub(crate) fn terms(&self) -> impl Iterator<Item = &Term<'tcx>> {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter())
    }

    fn terms_mut(&mut self) -> impl Iterator<Item = &mut Term<'tcx>> {
        self.requires.iter_mut().chain(self.ensures.iter_mut()).chain(self.variant.iter_mut())
    }

    pub(crate) fn ensures_conj(&self, tcx: TyCtxt<'tcx>) -> Term<'tcx> {
        let mut ensures = self.ensures.clone();

        let postcond = ensures.pop().unwrap_or(Term::mk_true(tcx));
        let postcond = ensures.into_iter().rfold(postcond, Term::conj);
        postcond
    }

    pub(crate) fn requires_conj(&self, tcx: TyCtxt<'tcx>) -> Term<'tcx> {
        let mut requires = self.requires.clone();

        let precond = requires.pop().unwrap_or(Term::mk_true(tcx));
        let precond = requires.into_iter().rfold(precond, Term::conj);
        precond
    }
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct ContractClauses {
    variant: Option<DefId>,
    requires: Vec<DefId>,
    ensures: Vec<DefId>,
    pub(crate) no_panic: bool,
    pub(crate) terminates: bool,
}

impl ContractClauses {
    pub(crate) fn new() -> Self {
        Self {
            variant: None,
            requires: Vec::new(),
            ensures: Vec::new(),
            no_panic: false,
            terminates: false,
        }
    }

    fn get_pre<'tcx>(self, ctx: &mut TranslationCtx<'tcx>) -> EarlyBinder<'tcx, PreContract<'tcx>> {
        let mut out = PreContract::default();
        for req_id in self.requires {
            log::trace!("require clause {:?}", req_id);
            let term = ctx.term(req_id).unwrap().clone();
            out.requires.push(term);
        }

        for ens_id in self.ensures {
            log::trace!("ensures clause {:?}", ens_id);
            let term = ctx.term(ens_id).unwrap().clone();
            out.ensures.push(term);
        }

        if let Some(var_id) = self.variant {
            log::trace!("variant clause {:?}", var_id);
            let term = ctx.term(var_id).unwrap().clone();
            out.variant = Some(term);
        };
        log::trace!("no_panic: {}", self.no_panic);
        out.no_panic = self.no_panic;
        log::trace!("terminates: {}", self.terminates);
        out.terminates = self.terminates;
        EarlyBinder::bind(out)
    }

    pub(crate) fn iter_ids(&self) -> impl Iterator<Item = DefId> + '_ {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter()).cloned()
    }
}

#[derive(Debug)]
struct ScopeTree(HashMap<SourceScope, (HashSet<(Symbol, Local)>, Option<SourceScope>)>);

impl ScopeTree {
    fn build<'tcx>(body: &Body<'tcx>) -> Self {
        use rustc_middle::mir::VarDebugInfoContents::Place;
        let mut scope_tree: HashMap<SourceScope, (HashSet<_>, Option<_>)> = Default::default();

        for var_info in &body.var_debug_info {
            // All variables in the DebugVarInfo should be user variables and thus be just locals
            let loc = match var_info.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!(),
            };
            let info = var_info.source_info;

            let scope = info.scope;
            let scope_data = &body.source_scopes[scope];

            let entry = scope_tree.entry(scope).or_default();

            let name = var_info.name;
            entry.0.insert((name, loc));

            if let Some(parent) = scope_data.parent_scope {
                entry.1 = Some(parent);
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }

        for (scope, scope_data) in body.source_scopes.iter_enumerated() {
            if let Some(parent) = scope_data.parent_scope {
                scope_tree.entry(scope).or_default().1 = Some(parent);
                scope_tree.entry(parent).or_default();
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }
        ScopeTree(scope_tree)
    }

    fn visible_locals(&self, scope: SourceScope) -> HashMap<Symbol, Local> {
        let mut locals = HashMap::new();
        let mut to_visit = Some(scope);

        while let Some(s) = to_visit.take() {
            let d = (HashSet::new(), None);
            self.0.get(&s).unwrap_or_else(|| &d).0.iter().for_each(|(id, loc)| {
                locals.entry(*id).or_insert(*loc);
            });
            to_visit = self.0.get(&s).unwrap_or_else(|| &d).1.clone();
        }

        locals
    }
}

// Turn a typing context into a substition.
pub(crate) fn inv_subst<'tcx>(
    body: &Body<'tcx>,
    locals: &HashMap<Local, Symbol>,
    info: SourceInfo,
) -> HashMap<Symbol, Term<'tcx>> {
    // let local_map = real_locals(tcx, body);
    let mut args = HashMap::new();

    let tree = ScopeTree::build(body);

    for (k, v) in tree.visible_locals(info.scope) {
        let loc = v;
        let ty = body.local_decls[loc].ty;
        let span = body.local_decls[loc].source_info.span;
        args.insert(k, Term { ty, span, kind: TermKind::Var(locals[&loc]) });
    }

    return args;
}

#[derive(Debug)]
#[allow(dead_code)]
pub enum SpecAttrError {
    InvalidTokens { id: DefId },
    InvalidTerm { id: DefId },
}

pub(crate) fn contract_clauses_of(
    ctx: &TranslationCtx,
    def_id: DefId,
) -> Result<ContractClauses, SpecAttrError> {
    use SpecAttrError::*;

    let attrs = ctx.get_attrs_unchecked(def_id);
    let mut contract = ContractClauses::new();

    // Attributes are given in reverse order. So we need to rever the list of
    // attributes to make sure requires/ensures clauses appear in the same
    // order in WhyML code as they appear in Rust code.
    for attr in attrs.iter().rev() {
        if !util::is_attr(attr, "clause") {
            continue;
        }

        let attr = attr.get_normal_item();

        // Stop using diagnostic item.
        // Use a custom HIR visitor which walks the attributes
        let get_creusot_item = || {
            let predicate_name = match &attr.args {
                AttrArgs::Eq(_, AttrArgsEq::Hir(l)) => l.symbol,
                _ => return Err(InvalidTokens { id: def_id }),
            };
            ctx.creusot_item(predicate_name).ok_or(InvalidTerm { id: def_id })
        };

        if attributes_matches(attr, &["creusot", "clause", "requires"]) {
            contract.requires.push(get_creusot_item()?)
        } else if attributes_matches(attr, &["creusot", "clause", "ensures"]) {
            contract.ensures.push(get_creusot_item()?);
        } else if attributes_matches(attr, &["creusot", "clause", "variant"]) {
            contract.variant = Some(get_creusot_item()?);
        } else if attributes_matches(attr, &["creusot", "clause", "terminates"]) {
            contract.terminates = true;
        } else if attributes_matches(attr, &["creusot", "clause", "no_panic"]) {
            contract.no_panic = true;
        }
    }

    Ok(contract)
}

fn attributes_matches(attr: &AttrItem, to_match: &[&str]) -> bool {
    let segments = &attr.path.segments;
    if segments.len() < to_match.len() {
        return false;
    }
    for (segment, &to_match) in std::iter::zip(segments, to_match) {
        if segment.ident.as_str() != to_match {
            return false;
        }
    }
    true
}

pub(crate) fn inherited_extern_spec<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let subst = GenericArgs::identity_for_item(ctx.tcx, def_id);
    try {
        if def_id.is_local() || ctx.extern_spec(def_id).is_some() {
            return None;
        }

        let assoc = ctx.opt_associated_item(def_id)?;
        let trait_ref = ctx.impl_trait_ref(assoc.container_id(ctx.tcx))?;
        let id = assoc.trait_item_def_id?;

        if ctx.extern_spec(id).is_none() {
            return None;
        }
        (id, trait_ref.instantiate(ctx.tcx, subst).args)
    }
}

pub(crate) fn contract_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> PreContract<'tcx> {
    if let Some(extern_spec) = ctx.extern_spec(def_id).cloned() {
        let mut contract =
            extern_spec.contract.get_pre(ctx).instantiate(ctx.tcx, extern_spec.subst);
        contract.subst(&extern_spec.arg_subst.iter().cloned().collect());
        contract.normalize(ctx.tcx, ctx.param_env(def_id))
    } else if let Some((parent_id, subst)) = inherited_extern_spec(ctx, def_id) {
        let spec = ctx.extern_spec(parent_id).cloned().unwrap();
        let mut contract = spec.contract.get_pre(ctx).instantiate(ctx.tcx, subst);
        contract.subst(&spec.arg_subst.iter().cloned().collect());
        contract.normalize(ctx.tcx, ctx.param_env(def_id))
    } else {
        let subst = GenericArgs::identity_for_item(ctx.tcx, def_id);
        let mut contract =
            contract_clauses_of(ctx, def_id).unwrap().get_pre(ctx).instantiate(ctx.tcx, subst);

        if contract.is_empty()
            && !def_id.is_local()
            && ctx.externs.get(def_id.krate).is_none()
            && util::item_type(ctx.tcx, def_id) == ItemType::Program
        {
            contract.extern_no_spec = true;
            contract.requires.push(Term::mk_false(ctx.tcx));
        }

        contract
    }
}

// These methods are allowed to cheat the purity restrictions because they are lang items we cannot redefine
pub(crate) fn is_overloaded_item(tcx: TyCtxt, def_id: DefId) -> bool {
    let def_path = tcx.def_path_str(def_id);

    def_path.ends_with("::ops::Mul::mul")
        || def_path.ends_with("::ops::Add::add")
        || def_path.ends_with("::ops::Sub::sub")
        || def_path.ends_with("::ops::Div::div")
        || def_path.ends_with("::ops::Rem::rem")
        || def_path.ends_with("::ops::Neg::neg")
        || def_path.ends_with("::boxed::Box::<T>::new")
        || def_path.ends_with("::ops::Deref::deref")
        || def_path.ends_with("::ops::DerefMut::deref_mut")
        || def_path.ends_with("Snapshot::<T>::from_fn")
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Purity {
    Program { terminates: bool, no_panic: bool },
    Logic { prophetic: bool },
}

impl Purity {
    pub(crate) fn of_def_id<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> Self {
        let is_snapshot = util::is_snapshot_closure(ctx.tcx, def_id);
        if (util::is_predicate(ctx.tcx, def_id) && util::is_prophetic(ctx.tcx, def_id))
            || (util::is_logic(ctx.tcx, def_id) && util::is_prophetic(ctx.tcx, def_id))
            || (util::is_spec(ctx.tcx, def_id) && !is_snapshot)
        {
            Purity::Logic { prophetic: true }
        } else if util::is_predicate(ctx.tcx, def_id)
            || util::is_logic(ctx.tcx, def_id)
            || is_snapshot
        {
            Purity::Logic { prophetic: false }
        } else {
            let contract = contract_of(ctx, def_id);
            let terminates = contract.terminates;
            let no_panic = contract.no_panic;
            Purity::Program { terminates, no_panic }
        }
    }

    fn can_call(self, other: Purity) -> bool {
        match (self, other) {
            (Purity::Logic { prophetic: true }, Purity::Logic { prophetic: false }) => true,
            (
                Purity::Program { no_panic, terminates },
                Purity::Program { no_panic: no_panic2, terminates: terminates2 },
            ) => no_panic <= no_panic2 && terminates <= terminates2,
            (ctx, call) => ctx == call,
        }
    }
}

impl Purity {
    fn as_str(&self) -> &'static str {
        match self {
            Purity::Program { terminates, no_panic } => match (*terminates, *no_panic) {
                (true, true) => "program (pure)",
                (true, false) => "program (terminates)",
                (false, true) => "program (no panic)",
                (false, false) => "program",
            },
            Purity::Logic { prophetic: false } => "logic",
            Purity::Logic { prophetic: true } => "prophetic logic",
        }
    }
}

pub(crate) struct PurityVisitor<'a, 'tcx> {
    pub(crate) ctx: &'a mut TranslationCtx<'tcx>,
    pub(crate) thir: &'a Thir<'tcx>,
    pub(crate) context: Purity,
}

impl<'a, 'tcx> PurityVisitor<'a, 'tcx> {
    fn purity(&mut self, fun: thir::ExprId, func_did: DefId) -> Purity {
        let stub = pearlite_stub(self.ctx.tcx, self.thir[fun].ty);

        if matches!(stub, Some(Stub::Fin))
            || (util::is_predicate(self.ctx.tcx, func_did)
                && util::is_prophetic(self.ctx.tcx, func_did))
            || (util::is_logic(self.ctx.tcx, func_did)
                && util::is_prophetic(self.ctx.tcx, func_did))
        {
            Purity::Logic { prophetic: true }
        } else if util::is_predicate(self.ctx.tcx, func_did)
            || util::is_logic(self.ctx.tcx, func_did)
            || util::get_builtin(self.ctx.tcx, func_did).is_some()
            || stub.is_some()
        {
            Purity::Logic { prophetic: false }
        } else {
            let contract = contract_of(self.ctx, func_did);
            let terminates = contract.terminates;
            let no_panic = contract.no_panic;
            Purity::Program { terminates, no_panic }
        }
    }
}

impl<'a, 'tcx> thir::visit::Visitor<'a, 'tcx> for PurityVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a thir::Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call { fun, .. } => {
                // FIXME: like in detect_recursion (MIR visitor), we would need to specialize the trait functions.
                if let &ty::FnDef(func_did, _) = self.thir[fun].ty.kind() {
                    let fn_purity = self.purity(fun, func_did);
                    if !self.context.can_call(fn_purity)
                        && !is_overloaded_item(self.ctx.tcx, func_did)
                    {
                        let (caller, callee) = match (self.context, fn_purity) {
                            (Purity::Program { .. }, Purity::Program { .. })
                            | (Purity::Logic { .. }, Purity::Logic { .. }) => {
                                (self.context.as_str(), fn_purity.as_str())
                            }
                            (Purity::Program { .. }, Purity::Logic { .. }) => ("program", "logic"),
                            (Purity::Logic { .. }, Purity::Program { .. }) => ("logic", "program"),
                        };
                        let msg = format!(
                            "called {callee} function `{}` in {caller} context",
                            self.ctx.def_path_str(func_did),
                        );

                        self.ctx.dcx().span_err(self.thir[fun].span, msg);
                    }
                } else if !matches!(self.context, Purity::Program { .. }) {
                    // TODO Add a "code" back in
                    self.ctx.dcx().span_fatal(expr.span, "non function call in logical context")
                }
            }
            ExprKind::Closure(box ClosureExpr { closure_id, .. }) => {
                if is_spec(self.ctx.tcx, closure_id.into()) {
                    return;
                }

                let (thir, expr) = self.ctx.thir_body(closure_id).unwrap_or_else(|_| {
                    Error::from(InternalError("Cannot fetch THIR body")).emit(self.ctx.tcx)
                });
                let thir = thir.borrow();

                thir::visit::walk_expr(
                    &mut PurityVisitor { ctx: self.ctx, thir: &thir, context: self.context },
                    &thir[expr],
                );
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr)
    }
}
