use crate::{
    backend::{
        program::borrow_generated_id,
        ty::{constructor, floatty_to_prelude, ity_to_prelude, translate_ty, uty_to_prelude},
        Why3Generator,
    },
    contracts_items::get_builtin,
    ctx::*,
    naming::ident_of,
    pearlite::{self, Literal, Pattern, PointerKind, Term, TermKind},
    translation::pearlite::{zip_binder, QuantKind, Trigger},
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{EarlyBinder, GenericArgsRef, Ty, TyCtxt, TyKind};
use rustc_span::DUMMY_SP;
use rustc_type_ir::{IntTy, UintTy};
use why3::{
    exp::{BinOp, Binder, Constant, Exp, Pattern as Pat},
    ty::Type,
    Ident,
};

pub(crate) fn lower_pure<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    term: &Term<'tcx>,
) -> Exp {
    let span = term.span;
    let mut term = Lower { ctx, names }.lower_term(term);
    term.reassociate();
    if let Some(attr) = names.span(span) {
        term.with_attr(attr)
    } else {
        term
    }
}

pub(crate) fn lower_pat<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    pat: &Pattern<'tcx>,
) -> Pat {
    Lower { ctx, names }.lower_pat(pat)
}

struct Lower<'a, 'tcx, N: Namer<'tcx>> {
    ctx: &'a Why3Generator<'tcx>,
    names: &'a N,
}
impl<'tcx, N: Namer<'tcx>> Lower<'_, 'tcx, N> {
    fn lower_term(&self, term: &Term<'tcx>) -> Exp {
        match &term.kind {
            TermKind::Lit(l) => lower_literal(self.ctx, self.names, l),
            TermKind::Cast { box arg } => match arg.ty.kind() {
                TyKind::Bool => {
                    let (fct_name, prelude_kind) = match term.ty.kind() {
                        TyKind::Int(ity) => ("of_bool", ity_to_prelude(self.ctx.tcx, *ity)),
                        TyKind::Uint(uty) => ("of_bool", uty_to_prelude(self.ctx.tcx, *uty)),
                        _ => self.ctx.crash_and_error(
                            DUMMY_SP,
                            "bool cast to non integral casts are currently unsupported",
                        ),
                    };

                    let qname = self.names.from_prelude(prelude_kind, fct_name);
                    Exp::Call(Box::new(Exp::qvar(qname)), vec![self.lower_term(arg)])
                }
                TyKind::Int(_) | TyKind::Uint(_) => {
                    // to
                    let (to_fct_name, to_prelude_kind) = match arg.ty.kind() {
                        TyKind::Int(ity) => (
                            if self.names.bitwise_mode() { "to_BV256" } else { "to_int" },
                            ity_to_prelude(self.ctx.tcx, *ity),
                        ),
                        TyKind::Uint(ity) => (
                            if self.names.bitwise_mode() { "to_BV256" } else { "to_int" },
                            uty_to_prelude(self.ctx.tcx, *ity),
                        ),
                        _ => self.ctx.crash_and_error(
                            DUMMY_SP,
                            &format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    // of
                    let (of_fct_name, of_prelude_kind) = match term.ty.kind() {
                        TyKind::Int(ity) => (
                            if self.names.bitwise_mode() { "of_BV256" } else { "of_int" },
                            ity_to_prelude(self.ctx.tcx, *ity),
                        ),
                        TyKind::Uint(ity) => (
                            if self.names.bitwise_mode() { "of_BV256" } else { "of_int" },
                            uty_to_prelude(self.ctx.tcx, *ity),
                        ),
                        _ => self.ctx.crash_and_error(
                            DUMMY_SP,
                            &format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    let to_qname = self.names.from_prelude(to_prelude_kind, to_fct_name);
                    let of_qname = self.names.from_prelude(of_prelude_kind, of_fct_name);

                    let to_exp =
                        Exp::Call(Box::new(Exp::qvar(to_qname)), vec![self.lower_term(arg)]);
                    Exp::Call(Box::new(Exp::qvar(of_qname)), vec![to_exp])
                }
                _ => self.ctx.crash_and_error(
                    DUMMY_SP,
                    "casting from a type that is not a boolean is not supported",
                ),
            },
            // FIXME: this is a weird dance.
            TermKind::Item(id, subst) => {
                let method = (*id, *subst);
                debug!("resolved_method={:?}", method);
                let clone = self.names.item(*id, subst);
                let item = match self.ctx.type_of(id).instantiate_identity().kind() {
                    TyKind::FnDef(_, _) => Exp::Tuple(Vec::new()),
                    _ => Exp::qvar(clone),
                };

                if matches!(self.ctx.def_kind(*id), DefKind::AssocConst) {
                    let ty = translate_ty(self.ctx, self.names, term.span, term.ty);
                    item.ascribe(ty)
                } else {
                    item
                }
            }
            TermKind::Var(v) => Exp::var(ident_of(*v)),
            TermKind::Binary { op, box lhs, box rhs } => {
                let lhs = self.lower_term(lhs);
                let rhs = self.lower_term(rhs);

                use pearlite::BinOp::*;
                match op {
                    Div => {
                        let ty_kind = term.creusot_ty().kind();
                        match ty_kind {
                            TyKind::Int(ity) => {
                                let prelude = ity_to_prelude(self.names.tcx(), *ity);
                                Exp::qvar(self.names.from_prelude(prelude, "sdiv"))
                                    .app(vec![lhs, rhs])
                            }
                            TyKind::Uint(uty) => {
                                let prelude = uty_to_prelude(self.names.tcx(), *uty);
                                Exp::qvar(self.names.from_prelude(prelude, "udiv"))
                                    .app(vec![lhs, rhs])
                            }
                            _ => Exp::qvar(self.names.from_prelude(PreludeModule::Int, "div"))
                                .app(vec![lhs, rhs]),
                        }
                    }
                    Rem => {
                        let ty_kind = term.creusot_ty().kind();
                        match ty_kind {
                            TyKind::Int(ity) => {
                                let prelude = ity_to_prelude(self.names.tcx(), *ity);
                                Exp::qvar(self.names.from_prelude(prelude, "srem"))
                                    .app(vec![lhs, rhs])
                            }
                            TyKind::Uint(uty) => {
                                let prelude = uty_to_prelude(self.names.tcx(), *uty);
                                Exp::qvar(self.names.from_prelude(prelude, "urem"))
                                    .app(vec![lhs, rhs])
                            }
                            _ => Exp::qvar(self.names.from_prelude(PreludeModule::Int, "mod"))
                                .app(vec![lhs, rhs]),
                        }
                    }
                    BitAnd | BitOr | BitXor | Shl | Shr => {
                        let ty_kind = term.creusot_ty().kind();
                        let prelude = match ty_kind {
                            TyKind::Int(ity) => ity_to_prelude(self.names.tcx(), *ity),
                            TyKind::Uint(uty) => uty_to_prelude(self.names.tcx(), *uty),
                            _ => unreachable!("the bitwise operator are only available on integer"),
                        };

                        let func_name = match (op, ty_kind) {
                            (BitAnd, _) => "bw_and",
                            (BitOr, _) => "bw_or",
                            (BitXor, _) => "bw_xor",
                            (Shl, _) => "lsl_bv",
                            (Shr, TyKind::Int(_)) => "asr_bv",
                            (Shr, TyKind::Uint(_)) => "lsr_bv",
                            _ => unreachable!(),
                        };

                        Exp::qvar(self.names.from_prelude(prelude, func_name)).app(vec![lhs, rhs])
                    }
                    _ => {
                        if matches!(op, Add | Sub | Mul | Le | Ge | Lt | Gt) {
                            self.names.import_prelude_module(PreludeModule::Int);
                        }
                        Exp::BinaryOp(binop_to_binop(*op), Box::new(lhs), Box::new(rhs))
                    }
                }
            }
            TermKind::Unary { op, box arg } => {
                if matches!(op, pearlite::UnOp::Neg) {
                    self.names.import_prelude_module(PreludeModule::Int);
                }
                let op = match op {
                    pearlite::UnOp::Not => why3::exp::UnOp::Not,
                    pearlite::UnOp::Neg => why3::exp::UnOp::Neg,
                };
                Exp::UnaryOp(op, Box::new(self.lower_term(arg)))
            }
            TermKind::Call { id, subst, args, .. } => {
                let mut args: Vec<_> = args.into_iter().map(|arg| self.lower_term(arg)).collect();

                if args.is_empty() {
                    args = vec![Exp::Tuple(vec![])];
                }

                let method = (*id, *subst);

                if is_identity_from(self.ctx.tcx, *id, method.1) {
                    return args.remove(0);
                }

                self.lookup_builtin(method, &mut args).unwrap_or_else(|| {
                    let clone = self.names.item(method.0, method.1);
                    Exp::qvar(clone).app(args)
                })
            }
            TermKind::Quant { kind, binder, box body, trigger } => {
                let bound = zip_binder(binder)
                    .map(|(s, t)| (s.to_string().into(), self.lower_ty(t)))
                    .collect();
                let body = self.lower_term(body);
                let trigger = self.lower_trigger(trigger);
                match kind {
                    QuantKind::Forall => Exp::forall_trig(bound, trigger, body),
                    QuantKind::Exists => Exp::exists_trig(bound, trigger, body),
                }
            }
            TermKind::Constructor { variant, fields, .. } => {
                let TyKind::Adt(adt, subst) = term.creusot_ty().kind() else { unreachable!() };
                let fields = fields.into_iter().map(|f| self.lower_term(f)).collect();
                constructor(self.names, fields, adt.variant(*variant).def_id, subst)
            }
            TermKind::Cur { box term } => {
                if term.creusot_ty().is_mutable_ptr() {
                    self.names.import_prelude_module(PreludeModule::Borrow);
                    self.lower_term(term).field("current")
                } else {
                    self.lower_term(term)
                }
            }
            TermKind::Fin { box term } => {
                self.names.import_prelude_module(PreludeModule::Borrow);
                self.lower_term(term).field("final")
            }
            TermKind::Impl { box lhs, box rhs } => {
                self.lower_term(lhs).implies(self.lower_term(rhs))
            }
            TermKind::Old { box term } => Exp::Old(Box::new(self.lower_term(term))),
            TermKind::Match { box scrutinee, arms } => {
                if scrutinee.ty.peel_refs().is_bool() {
                    let (true_br, false_br) = if let Pattern::Boolean(true) = arms[0].0 {
                        (&arms[0].1, &arms[1].1)
                    } else {
                        (&arms[1].1, &arms[0].1)
                    };
                    Exp::if_(
                        self.lower_term(scrutinee),
                        self.lower_term(true_br),
                        self.lower_term(false_br),
                    )
                } else {
                    let _ = self.lower_ty(scrutinee.ty);
                    let arms = arms
                        .iter()
                        .map(|(pat, body)| (self.lower_pat(pat), self.lower_term(body)))
                        .collect();
                    Exp::Match(Box::new(self.lower_term(scrutinee)), arms)
                }
            }
            TermKind::Let { pattern, box arg, box body } => Exp::Let {
                pattern: self.lower_pat(pattern),
                arg: Box::new(self.lower_term(arg)),
                body: Box::new(self.lower_term(body)),
            },
            TermKind::Tuple { fields } => {
                Exp::Tuple(fields.into_iter().map(|f| self.lower_term(f)).collect())
            }
            TermKind::Projection { box lhs, name } => {
                let lhs_low = self.lower_term(lhs);

                let field = match lhs.creusot_ty().kind() {
                    TyKind::Closure(did, substs) => self.names.field(*did, substs, *name),
                    TyKind::Adt(def, substs) => self.names.field(def.did(), substs, *name),
                    TyKind::Tuple(f) => {
                        let mut fields = vec![Pat::Wildcard; f.len()];
                        fields[name.as_usize()] = Pat::VarP("a".into());

                        return Exp::Let {
                            pattern: Pat::TupleP(fields),
                            arg: Box::new(lhs_low),
                            body: Box::new(Exp::var("a")),
                        };
                    }
                    k => unreachable!("Projection from {k:?}"),
                };

                lhs_low.field(&field.as_ident())
            }
            TermKind::Closure { body, .. } => {
                let TyKind::Closure(id, subst) = term.creusot_ty().kind() else {
                    unreachable!("closure has non closure type")
                };
                let body = self.lower_term(&*body);

                let mut binders = Vec::new();
                let sig = self.ctx.sig(*id).clone();
                let sig = EarlyBinder::bind(sig).instantiate(self.ctx.tcx, subst);
                for arg in sig.inputs.iter().skip(1) {
                    let nm = Ident::build(&arg.0.to_string());
                    let ty = self.names.normalize(self.ctx, arg.2);
                    binders.push(Binder::typed(nm, self.lower_ty(ty)))
                }

                Exp::Abs(binders, Box::new(body))
            }
            TermKind::Reborrow { cur, fin, inner, projection } => {
                let inner = self.lower_term(&*inner);
                let borrow_id = borrow_generated_id(self.names, inner, &projection, |x| {
                    if matches!(x.ty.kind(), TyKind::Uint(UintTy::Usize)) {
                        let qname = self
                            .names
                            .from_prelude(uty_to_prelude(self.ctx.tcx, UintTy::Usize), "t'int");
                        Exp::Call(Box::new(Exp::qvar(qname)), vec![self.lower_term(x)])
                    } else {
                        self.lower_term(x)
                    }
                });

                Exp::qvar(self.names.from_prelude(PreludeModule::Borrow, "borrow_logic")).app(vec![
                    self.lower_term(&*cur),
                    self.lower_term(&*fin),
                    borrow_id,
                ])
            }
            TermKind::Assert { .. } => {
                // Discard cond, use unit
                Exp::Tuple(vec![])
            }
            TermKind::Precondition { item, args, params } => {
                let params: Vec<_> = params.iter().map(|p| self.lower_term(p)).collect();
                let mut sym = self.names.item(*item, args);
                sym.name = format!("{}'pre", &*sym.name).into();

                Exp::qvar(sym).app(params)
            }
            TermKind::Postcondition { item, args, params } => {
                let params: Vec<_> = params.iter().map(|p| self.lower_term(p)).collect();
                let mut sym = self.names.item(*item, args);
                sym.name = format!("{}'post'return'", &*sym.name).into();
                Exp::qvar(sym).app(params)
            }
        }
    }

    fn lower_pat(&self, pat: &Pattern<'tcx>) -> Pat {
        match pat {
            Pattern::Constructor { variant, fields, substs } => {
                let fields = fields.into_iter().map(|pat| self.lower_pat(pat)).collect();
                if self.ctx.def_kind(variant) == DefKind::Variant {
                    Pat::ConsP(self.names.constructor(*variant, *substs), fields)
                } else if fields.len() == 0 {
                    Pat::TupleP(vec![])
                } else {
                    Pat::RecP(
                        fields
                            .into_iter()
                            .enumerate()
                            .map(|(i, f)| {
                                (self.names.field(*variant, substs, i.into()).as_ident(), f)
                            })
                            .filter(|(_, f)| !matches!(f, Pat::Wildcard))
                            .collect(),
                    )
                }
            }
            Pattern::Wildcard => Pat::Wildcard,
            Pattern::Binder(name) => Pat::VarP(name.to_string().into()),
            Pattern::Boolean(b) => {
                if *b {
                    Pat::mk_true()
                } else {
                    Pat::mk_false()
                }
            }
            Pattern::Tuple(pats) => {
                Pat::TupleP(pats.into_iter().map(|pat| self.lower_pat(pat)).collect())
            }
            Pattern::Deref { pointee, kind } => match kind {
                PointerKind::Box | PointerKind::Shr => self.lower_pat(pointee),
                PointerKind::Mut => Pat::RecP(vec![("current".into(), self.lower_pat(pointee))]),
            },
        }
    }

    fn lower_ty(&self, ty: Ty<'tcx>) -> Type {
        translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty)
    }

    pub(crate) fn lookup_builtin(
        &self,
        method: (DefId, GenericArgsRef<'tcx>),
        args: &Vec<Exp>,
    ) -> Option<Exp> {
        let def_id = method.0;
        let substs = method.1;

        if get_builtin(self.ctx.tcx, def_id).is_some() {
            return Some(Exp::qvar(self.names.item(def_id, substs)).app(args.clone()));
        }
        None
    }

    fn lower_trigger(&self, triggers: &[Trigger<'tcx>]) -> Vec<why3::exp::Trigger> {
        triggers
            .iter()
            .map(|x| why3::exp::Trigger(x.0.iter().map(|x| self.lower_term(x)).collect()))
            .collect()
    }
}

pub(crate) fn lower_literal<'tcx, N: Namer<'tcx>>(
    ctx: &TranslationCtx<'tcx>,
    names: &N,
    lit: &Literal<'tcx>,
) -> Exp {
    match *lit {
        Literal::Integer(i) => Constant::Int(i, None).into(),
        Literal::MachSigned(mut i, ity) => {
            let why_ty = Type::TConstructor(names.from_prelude(ity_to_prelude(ctx.tcx, ity), "t"));
            if names.bitwise_mode() {
                // In bitwise mode, integers are bit vectors, whose literals are always unsigned
                if i < 0 && ity != IntTy::I128 {
                    let target_width = ctx.tcx.sess.target.pointer_width;
                    i += 1 << ity.normalize(target_width).bit_width().unwrap();
                }
                Constant::Uint(i as u128, Some(why_ty)).into()
            } else {
                Constant::Int(i, Some(why_ty)).into()
            }
        }
        Literal::MachUnsigned(u, uty) => {
            let why_ty = Type::TConstructor(names.from_prelude(uty_to_prelude(ctx.tcx, uty), "t"));
            Constant::Uint(u, Some(why_ty)).into()
        }
        Literal::Bool(true) => Constant::const_true().into(),
        Literal::Bool(false) => Constant::const_false().into(),
        Literal::Char(c) => {
            let of_int = names.from_prelude(PreludeModule::Char, "of_int");
            Exp::Call(
                Box::new(Exp::qvar(of_int)),
                vec![Constant::Int(c as u32 as i128, None).into()],
            )
        }
        Literal::Function(id, subst) => {
            names.item(id, subst);
            Exp::Tuple(Vec::new())
        }
        Literal::Float(ref f, fty) => {
            let why_ty = Type::TConstructor(names.from_prelude(floatty_to_prelude(fty), "t"));
            Constant::Float(f.0, Some(why_ty)).into()
        }
        Literal::ZST => Exp::Tuple(Vec::new()),
        Literal::String(ref string) => Constant::String(string.clone()).into(),
    }
}

pub(crate) fn binop_to_binop(op: pearlite::BinOp) -> why3::exp::BinOp {
    match op {
        pearlite::BinOp::Add => BinOp::Add,
        pearlite::BinOp::Sub => BinOp::Sub,
        pearlite::BinOp::Mul => BinOp::Mul,
        pearlite::BinOp::Lt => BinOp::Lt,
        pearlite::BinOp::Le => BinOp::Le,
        pearlite::BinOp::Gt => BinOp::Gt,
        pearlite::BinOp::Ge => BinOp::Ge,
        pearlite::BinOp::Eq => BinOp::Eq,
        pearlite::BinOp::Ne => BinOp::Ne,
        pearlite::BinOp::And => BinOp::LogAnd,
        pearlite::BinOp::Or => BinOp::LogOr,
        pearlite::BinOp::BitAnd => BinOp::BitAnd,
        pearlite::BinOp::BitOr => BinOp::BitOr,
        pearlite::BinOp::BitXor => BinOp::BitXor,
        pearlite::BinOp::Shl => BinOp::Shl,
        pearlite::BinOp::Shr => BinOp::Shr,
        pearlite::BinOp::Div => todo!("Refactor binop_to_binop to support Div"),
        pearlite::BinOp::Rem => todo!("Refactor binop_to_binop to support Rem"),
    }
}

fn is_identity_from<'tcx>(tcx: TyCtxt<'tcx>, id: DefId, subst: GenericArgsRef<'tcx>) -> bool {
    if tcx.def_path_str(id) == "std::convert::From::from" && subst.len() == 1 {
        let out_ty: Ty<'tcx> = tcx.fn_sig(id).no_bound_vars().unwrap().output().skip_binder();
        return subst[0].expect_ty() == EarlyBinder::bind(out_ty).instantiate(tcx, subst);
    }
    false
}
