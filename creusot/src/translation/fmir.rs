use crate::{
    backend::projections::projection_ty,
    translation::pearlite::{PIdent, Term},
};
use indexmap::IndexMap;
use rustc_abi::VariantIdx;
use rustc_ast_ir::{try_visit, visit::VisitorResult};
use rustc_hir::def_id::DefId;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{
        self, BasicBlock, BinOp, Local, OUTERMOST_SOURCE_SCOPE, PlaceTy, Promoted, SourceScope,
        UnOp, VarDebugInfoContents,
    },
    ty::{AdtDef, GenericArgsRef, Ty, TyCtxt, TypeFoldable, TypeVisitable},
};
use rustc_span::{Span, Symbol};
use std::collections::HashMap;
use why3::Ident;

pub(crate) type ProjectionElem<'tcx> = rustc_middle::mir::ProjectionElem<PIdent, Ty<'tcx>>;

/// The equivalent of [`mir::Place`], but for fMIR
#[derive(Clone, Debug, PartialEq, Eq, Hash, TypeFoldable, TypeVisitable)]
pub struct Place<'tcx> {
    #[type_visitable(ignore)]
    #[type_foldable(identity)]
    pub(crate) local: Ident,
    pub(crate) projections: Box<[ProjectionElem<'tcx>]>,
}

/// The equivalent of [`mir::PlaceRef`], but for fMIR
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct PlaceRef<'a, 'tcx> {
    pub(crate) local: Ident,
    pub(crate) projection: &'a [ProjectionElem<'tcx>],
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> Ty<'tcx> {
        let mut ty = PlaceTy::from_ty(locals[&self.local].ty);

        for p in self.projections.iter() {
            ty = projection_ty(ty, tcx, p);
        }

        ty.ty
    }

    pub(crate) fn as_symbol(&self) -> Option<Ident> {
        if self.projections.is_empty() { Some(self.local) } else { None }
    }

    pub(crate) fn iter_projections(
        &self,
    ) -> impl DoubleEndedIterator<Item = (PlaceRef<'_, 'tcx>, ProjectionElem<'tcx>)> + '_ {
        self.projections.iter().enumerate().map(move |(i, proj)| {
            let base = PlaceRef { local: self.local, projection: &self.projections[..i] };
            (base, *proj)
        })
    }

    pub fn last_projection(&self) -> Option<(PlaceRef<'_, 'tcx>, ProjectionElem<'tcx>)> {
        if let &[ref proj_base @ .., elem] = &self.projections[..] {
            Some((PlaceRef { local: self.local, projection: proj_base }, elem))
        } else {
            None
        }
    }
}

impl<'tcx> PlaceRef<'_, 'tcx> {
    pub(crate) fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> PlaceTy<'tcx> {
        let mut ty = PlaceTy::from_ty(locals[&self.local].ty);

        for p in self.projection.iter() {
            ty = projection_ty(ty, tcx, p);
        }

        ty
    }
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub enum StatementKind<'tcx> {
    Assignment(Place<'tcx>, RValue<'tcx>),
    Resolve {
        did: DefId,
        subst: GenericArgsRef<'tcx>,
        pl: Place<'tcx>,
    },
    Assertion {
        cond: Term<'tcx>,
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        msg: String,
        trusted: bool,
    },
    // Todo: fold into `Assertion`
    AssertTyInv {
        pl: Place<'tcx>,
    },
    Call(Place<'tcx>, DefId, GenericArgsRef<'tcx>, Box<[Operand<'tcx>]>),
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub(crate) struct Statement<'tcx> {
    pub(crate) kind: StatementKind<'tcx>,
    pub(crate) span: Span,
}

// TODO: Add shared borrows?
#[derive(Clone, Copy, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum BorrowKind {
    /// Ordinary mutable borrows
    Mut,
    /// The source of this borrow is not used after the reborrow, and thus we can
    /// inherit the prophecy identifier.
    ///
    /// The second field is an index in `place.projection`: see
    /// [`NotFinalPlaces::is_final_at`](crate::analysis::NotFinalPlaces::is_final_at).
    Final(usize),
}

#[derive(Clone, Copy, Debug, TypeFoldable, TypeVisitable, PartialEq, Eq)]
pub enum TrivialInv {
    Trivial,
    NonTrivial,
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub enum RValue<'tcx> {
    Snapshot(Term<'tcx>),
    Borrow(BorrowKind, Place<'tcx>, TrivialInv),
    Operand(Operand<'tcx>),
    BinOp(BinOp, Operand<'tcx>, Operand<'tcx>),
    UnaryOp(UnOp, Operand<'tcx>),
    Constructor(DefId, GenericArgsRef<'tcx>, Box<[Operand<'tcx>]>),
    Cast(Operand<'tcx>, Ty<'tcx>, Ty<'tcx>),
    Tuple(Box<[Operand<'tcx>]>),
    Array(Box<[Operand<'tcx>]>),
    Repeat(Operand<'tcx>, Operand<'tcx>),
    Ptr(Place<'tcx>),
}

impl RValue<'_> {
    /// Returns false if the expression generates verification conditions
    pub fn is_pure(&self) -> bool {
        match self {
            RValue::Operand(_) => true,
            RValue::BinOp(
                BinOp::Add
                | BinOp::AddUnchecked
                | BinOp::Mul
                | BinOp::MulUnchecked
                | BinOp::Rem
                | BinOp::Div
                | BinOp::Sub
                | BinOp::SubUnchecked
                | BinOp::Shl
                | BinOp::ShlUnchecked
                | BinOp::Shr
                | BinOp::ShrUnchecked
                | BinOp::Offset,
                _,
                _,
            ) => false,
            RValue::BinOp(
                BinOp::AddWithOverflow
                | BinOp::SubWithOverflow
                | BinOp::MulWithOverflow
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
                | BinOp::Cmp
                | BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge,
                _,
                _,
            ) => true,
            RValue::UnaryOp(UnOp::Neg, _) => false,
            RValue::UnaryOp(UnOp::Not | UnOp::PtrMetadata, _) => true,
            RValue::Constructor(_, _, _) => true,
            RValue::Cast(_, _, _) => false,
            RValue::Tuple(_) => true,
            RValue::Array(_) => true,
            RValue::Repeat(_, _) => true,
            RValue::Snapshot(_) => true,
            RValue::Borrow(_, _, _) => true,
            RValue::Ptr(_) => true,
        }
    }
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub enum Operand<'tcx> {
    Move(Place<'tcx>),
    Copy(Place<'tcx>),
    Term(Term<'tcx>),
    /// Either:
    /// - Inline `const { ... }` expressions (`Option<Promoted>` is `None` and `Option<GenericArgsRef>` is `Some`)
    /// - Promoted constants (`Option<Promoted>` is `Some` and `Option<GenericArgsRef>` is `None`)
    InlineConst(DefId, Option<Promoted>, Option<GenericArgsRef<'tcx>>, Ty<'tcx>),
}

impl<'tcx> Operand<'tcx> {
    pub fn inline_const(def_id: DefId, subst: GenericArgsRef<'tcx>, ty: Ty<'tcx>) -> Self {
        Operand::InlineConst(def_id, None, Some(subst), ty)
    }

    pub fn promoted(def_id: DefId, promoted: Promoted, ty: Ty<'tcx>) -> Self {
        Operand::InlineConst(def_id, Some(promoted), None, ty)
    }

    pub fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> Ty<'tcx> {
        match self {
            Operand::Move(pl) => pl.ty(tcx, locals),
            Operand::Copy(pl) => pl.ty(tcx, locals),
            Operand::Term(t) => t.ty,
            Operand::InlineConst(_, _, _, ty) => *ty,
        }
    }
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(self::Operand<'tcx>, Branches<'tcx>),
    Return,
    Abort(Span),
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub enum Branches<'tcx> {
    Int(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        Box<[(i128, BasicBlock)]>,
        BasicBlock,
    ),
    Uint(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        Box<[(u128, BasicBlock)]>,
        BasicBlock,
    ),
    Constructor(
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        AdtDef<'tcx>,
        GenericArgsRef<'tcx>,
        #[type_visitable(ignore)]
        #[type_foldable(identity)]
        Box<[(VariantIdx, BasicBlock)]>,
        Option<BasicBlock>,
    ),
    Bool(BasicBlock, BasicBlock),
}

impl Terminator<'_> {
    pub fn targets(&self) -> Box<dyn Iterator<Item = BasicBlock> + '_> {
        use std::iter::*;
        match self {
            Terminator::Goto(bb) => Box::new(once(*bb)),
            Terminator::Switch(_, brs) => match brs {
                Branches::Int(brs, def) => Box::new(brs.iter().map(|(_, b)| *b).chain(once(*def))),
                Branches::Uint(brs, def) => Box::new(brs.iter().map(|(_, b)| *b).chain(once(*def))),
                Branches::Constructor(_, _, brs, def) => {
                    Box::new(brs.iter().map(|(_, b)| *b).chain(*def))
                }
                Branches::Bool(f, t) => Box::new([*f, *t].into_iter()),
            },
            Terminator::Return => Box::new(empty()),
            Terminator::Abort(_) => Box::new(empty()),
        }
    }

    pub fn targets_mut(&mut self) -> Box<dyn Iterator<Item = &mut BasicBlock> + '_> {
        use std::iter::*;
        match self {
            Terminator::Goto(bb) => Box::new(once(bb)),
            Terminator::Switch(_, brs) => match brs {
                Branches::Int(brs, def) => {
                    Box::new(brs.iter_mut().map(|(_, b)| b).chain(once(def)))
                }
                Branches::Uint(brs, def) => {
                    Box::new(brs.iter_mut().map(|(_, b)| b).chain(once(def)))
                }
                Branches::Constructor(_, _, brs, def) => {
                    Box::new(brs.iter_mut().map(|(_, b)| b).chain(def))
                }
                Branches::Bool(f, t) => Box::new([f, t].into_iter()),
            },
            Terminator::Return => Box::new(empty()),
            Terminator::Abort(_) => Box::new(empty()),
        }
    }
}

impl Branches<'_> {
    pub fn targets_mut(&mut self) -> Box<dyn Iterator<Item = &mut BasicBlock> + '_> {
        use std::iter::*;
        match self {
            Branches::Int(brs, def) => Box::new(brs.iter_mut().map(|(_, b)| b).chain(once(def))),
            Branches::Uint(brs, def) => Box::new(brs.iter_mut().map(|(_, b)| b).chain(once(def))),
            Branches::Constructor(_, _, brs, def) => {
                Box::new(brs.iter_mut().map(|(_, b)| b).chain(def.as_mut()))
            }
            Branches::Bool(f, t) => Box::new([f, t].into_iter()),
        }
    }
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub struct Invariant<'tcx> {
    pub(crate) body: Term<'tcx>,
    /// Label ("explanation") for the corresponding Why3 subgoal, including the "expl:" prefix
    #[type_visitable(ignore)]
    #[type_foldable(identity)]
    pub(crate) expl: String,
}

/// A loop variant
#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub(crate) struct Variant<'tcx> {
    /// The term that should decrease
    pub(crate) term: Term<'tcx>,
    /// The name of the variable that holds the previous value of the term.
    pub(crate) old_name: PIdent,
}

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub struct Block<'tcx> {
    pub(crate) invariants: Vec<Invariant<'tcx>>,
    /// An eventual variant that should be checked before `continue`ing a loop.
    ///
    /// This is `Some` when the block is the loop head.
    pub(crate) variant: Option<Variant<'tcx>>,
    pub(crate) stmts: Vec<Statement<'tcx>>,
    pub(crate) terminator: Terminator<'tcx>,
}

pub type LocalDecls<'tcx> = IndexMap<Ident, LocalDecl<'tcx>>;

#[derive(Clone, Debug, TypeFoldable, TypeVisitable)]
pub struct LocalDecl<'tcx> {
    // Original MIR local
    pub(crate) span: Span,
    pub(crate) ty: Ty<'tcx>,
    // Is this a MIR temporary?
    pub(crate) temp: bool,
    // Is this declaration a function argument or return place?
    pub(crate) arg: bool,
}

#[derive(Clone, Debug)]
pub struct Body<'tcx> {
    // TODO: Split into return local, args, and true locals?
    // TODO: Remove usage of `LocalIdent`.
    pub(crate) locals: LocalDecls<'tcx>,
    /// Locals that hold the previous values of loop variants
    pub(crate) variant_locals: Vec<(PIdent, Ty<'tcx>, Span)>,
    /// Names for the eventual variant for the function.
    ///
    /// This is the name of the variable holding the variant's value at the
    /// start of the function
    pub(crate) function_variant: PIdent,
    pub(crate) blocks: IndexMap<BasicBlock, Block<'tcx>>,
    pub(crate) fresh: usize,
    pub(crate) block_spans: HashMap<BasicBlock, Span>,
}

impl<'tcx> TypeVisitable<TyCtxt<'tcx>> for Body<'tcx> {
    fn visit_with<V>(&self, v: &mut V) -> <V as rustc_middle::ty::TypeVisitor<TyCtxt<'tcx>>>::Result
    where
        V: rustc_middle::ty::TypeVisitor<TyCtxt<'tcx>>,
    {
        for local in self.locals.values() {
            try_visit!(local.visit_with(v));
        }
        for block in self.blocks.values() {
            try_visit!(block.visit_with(v));
        }
        VisitorResult::output()
    }
}

impl<'tcx> TypeFoldable<TyCtxt<'tcx>> for Body<'tcx> {
    fn fold_with<F>(self, f: &mut F) -> Self
    where
        F: rustc_middle::ty::TypeFolder<TyCtxt<'tcx>>,
    {
        Self {
            variant_locals: self.variant_locals.fold_with(f),
            function_variant: self.function_variant.fold_with(f),
            fresh: self.fresh,
            locals: self.locals.into_iter().map(|(k, v)| (k, v.fold_with(f))).collect(),
            blocks: self.blocks.into_iter().map(|(k, v)| (k, v.fold_with(f))).collect(),
            block_spans: self.block_spans,
        }
    }

    fn try_fold_with<F>(self, f: &mut F) -> Result<Self, F::Error>
    where
        F: rustc_middle::ty::FallibleTypeFolder<TyCtxt<'tcx>>,
    {
        Ok(Self {
            variant_locals: self.variant_locals.try_fold_with(f)?,
            function_variant: self.function_variant.try_fold_with(f)?,
            fresh: self.fresh,
            locals: self
                .locals
                .into_iter()
                .map(|(k, v)| v.try_fold_with(f).map(|v| (k, v)))
                .collect::<Result<_, _>>()?,
            blocks: self
                .blocks
                .into_iter()
                .map(|(k, v)| v.try_fold_with(f).map(|v| (k, v)))
                .collect::<Result<_, _>>()?,
            block_spans: self.block_spans,
        })
    }
}

/// The scope tree is MIR metadata that we use to map HIR variables (`HirId`)
/// to MIR variables (`Local`, `Place`).
///
/// The MIR we want to translate may contain fragments of Pearlite (from
/// `proof_assert!`, `snapshot!`), whose variables come from `HirId`.
/// We must substitute those variables with their corresponding MIR place.
/// Unfortunately, rustc does not maintain a mapping from `HirId` to MIR
/// places. We recover that information indirectly from scope trees.
///
/// The scope tree is the shape of the binding structure of the HIR term.
/// A node in the scope tree (`SourceScope`) corresponds to a binder in HIR
/// (let, match, closure), and contains a mapping from "source variables"
/// to MIR places. A variable is in scope at a node if it is bound by that
/// node or one of its ancestors.
///
/// Those "source variables" are encoded as `rustc_span::Ident`, which are
/// pairs of string and span. The sad thing is that it is not `HirId`,
/// which would have made things simpler. Because of macros, multiple
/// binders may have the same `rustc_span::Ident`, so we must reimplement
/// the handling of shadowing.
///
/// When we encounter a Pearlite term (from `proof_assert!` or `snapshot!`) in
/// a MIR block, we substitute each free variables as follows: (1) extract
/// `rustc_span::Ident` from its `HirId`, (2) find the closest binder for that
/// `rustc_span::Ident` in the source tree above the `SourceScope` attached to
/// the surrounding MIR block (this is precomputed by `ScopeTree::visible_places`),
/// (3) get the `Place` from that binder to replace the variable.
/// This happens in `inline_pearlite_subst`.
#[derive(Debug)]
pub struct ScopeTree(
    HashMap<SourceScope, (Vec<(rustc_span::Ident, Option<PIdent>)>, Option<SourceScope>)>,
);

impl ScopeTree {
    pub fn empty() -> Self {
        ScopeTree(HashMap::new())
    }

    /// Extract the scope tree from a MIR body.
    pub fn build<'tcx>(body: &mir::Body<'tcx>, locals: &HashMap<Local, (Symbol, Ident)>) -> Self {
        let mut scope_tree = ScopeTree(HashMap::new());

        for var_info in &body.var_debug_info {
            // All variables in the DebugVarInfo should be user variables and thus be just places
            // If the variable is local to the function the place will have no projections.
            // Else this is a captured variable, and we don't need to consider it.
            let VarDebugInfoContents::Place(p) = var_info.value else { panic!() };
            let t = if p.projection.is_empty() { Some(locals[&p.local].1.into()) } else { None };

            let scope = var_info.source_info.scope;
            let entry = scope_tree.0.entry(scope).or_default();

            let ident = rustc_span::Ident { name: var_info.name, span: var_info.source_info.span };
            entry.0.push((ident, t));

            if let Some(parent) = body.source_scopes[scope].parent_scope {
                entry.1 = Some(parent);
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }

        for (scope, scope_data) in body.source_scopes.iter_enumerated() {
            if let Some(parent) = scope_data.parent_scope {
                scope_tree.0.entry(scope).or_default().1 = Some(parent);
                scope_tree.0.entry(parent).or_default();
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }

        // body.source_scopes is empty (not even a root) for functions without locals
        scope_tree.0.entry(OUTERMOST_SOURCE_SCOPE).or_default();

        scope_tree
    }

    /// Obtain MIR locals for HIR variables visible in a given scope.
    pub fn visible_locals(
        &self,
        mut scope: SourceScope,
    ) -> HashMap<rustc_span::Ident, Option<PIdent>> {
        let mut locals = HashMap::new();
        loop {
            let (places, parent) = self.0.get(&scope).unwrap();
            for (id, pid) in places {
                // If multiple binders have the same identifier, use the closest one
                locals.entry(*id).or_insert_with(|| *pid);
            }
            let Some(parent) = parent else { break };
            scope = *parent
        }

        locals
    }
}

pub(crate) trait FmirVisitor<'tcx>: Sized {
    fn visit_body(&mut self, body: &Body<'tcx>) {
        super_visit_body(self, body);
    }

    fn visit_block(&mut self, block: &Block<'tcx>) {
        super_visit_block(self, block);
    }

    fn visit_stmt(&mut self, stmt: &Statement<'tcx>) {
        super_visit_stmt(self, stmt);
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>) {
        super_visit_operand(self, operand);
    }

    fn visit_place(&mut self, place: &Place<'tcx>) {
        super_visit_place(self, place);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>) {
        super_visit_terminator(self, terminator);
    }

    fn visit_term(&mut self, _: &Term<'tcx>) {}

    fn visit_rvalue(&mut self, rval: &RValue<'tcx>) {
        super_visit_rvalue(self, rval);
    }
}

pub(crate) fn super_visit_body<'tcx, V: FmirVisitor<'tcx>>(visitor: &mut V, body: &Body<'tcx>) {
    for block in &body.blocks {
        visitor.visit_block(block.1);
    }
}

pub(crate) fn super_visit_block<'tcx, V: FmirVisitor<'tcx>>(visitor: &mut V, block: &Block<'tcx>) {
    for stmt in &block.stmts {
        visitor.visit_stmt(stmt);
    }

    visitor.visit_terminator(&block.terminator);
}

pub(crate) fn super_visit_stmt<'tcx, V: FmirVisitor<'tcx>>(
    visitor: &mut V,
    stmt: &Statement<'tcx>,
) {
    match &stmt.kind {
        StatementKind::Assignment(place, rval) => {
            visitor.visit_place(place);
            visitor.visit_rvalue(rval);
        }
        StatementKind::Resolve { pl, .. } => {
            visitor.visit_place(pl);
        }
        StatementKind::Assertion { cond, .. } => {
            visitor.visit_term(cond);
        }
        StatementKind::AssertTyInv { pl, .. } => {
            visitor.visit_place(pl);
        }
        StatementKind::Call(place, _, _, operands) => {
            visitor.visit_place(place);
            for operand in operands {
                visitor.visit_operand(operand);
            }
        }
    }
}

pub(crate) fn super_visit_operand<'tcx, V: FmirVisitor<'tcx>>(
    visitor: &mut V,
    operand: &Operand<'tcx>,
) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            visitor.visit_place(place);
        }
        Operand::Term(_) | Operand::InlineConst(_, _, _, _) => (),
    }
}

pub(crate) fn super_visit_place<'tcx, V: FmirVisitor<'tcx>>(_: &mut V, _: &Place<'tcx>) {}

pub(crate) fn super_visit_terminator<'tcx, V: FmirVisitor<'tcx>>(
    visitor: &mut V,
    terminator: &Terminator<'tcx>,
) {
    match terminator {
        Terminator::Goto(_) => (),
        Terminator::Switch(op, _) => {
            visitor.visit_operand(op);
        }
        Terminator::Return => (),
        Terminator::Abort(_) => (),
    }
}

pub(crate) fn super_visit_rvalue<'tcx, V: FmirVisitor<'tcx>>(visitor: &mut V, rval: &RValue<'tcx>) {
    match rval {
        RValue::Snapshot(term) => {
            visitor.visit_term(term);
        }
        RValue::Borrow(_, place, _) => {
            visitor.visit_place(place);
        }
        RValue::Operand(op) => {
            visitor.visit_operand(op);
        }
        RValue::BinOp(_, op1, op2) => {
            visitor.visit_operand(op1);
            visitor.visit_operand(op2);
        }
        RValue::UnaryOp(_, op) => {
            visitor.visit_operand(op);
        }
        RValue::Constructor(_, _, ops) => {
            for op in ops {
                visitor.visit_operand(op);
            }
        }
        RValue::Cast(op, _, _) => {
            visitor.visit_operand(op);
        }
        RValue::Tuple(ops) => {
            for op in ops {
                visitor.visit_operand(op);
            }
        }
        RValue::Array(ops) => {
            for op in ops {
                visitor.visit_operand(op);
            }
        }
        RValue::Repeat(op1, op2) => {
            visitor.visit_operand(op1);
            visitor.visit_operand(op2);
        }
        RValue::Ptr(pl) => {
            visitor.visit_place(pl);
        }
    }
}
