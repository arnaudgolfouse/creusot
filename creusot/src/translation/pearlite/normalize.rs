use crate::{
    contracts_items::{get_builtin, is_box_new},
    pearlite::{self, Literal, Term, TermKind},
    traits::TraitResolved,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{TyCtxt, TypingEnv};

use super::{super_visit_mut_term, BinOp, TermVisitorMut};

pub(crate) fn normalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    mut term: Term<'tcx>,
) -> Term<'tcx> {
    NormalizeTerm { typing_env, tcx }.visit_mut_term(&mut term);
    let term = tcx.normalize_erasing_regions(typing_env, term);
    term
}

struct NormalizeTerm<'tcx> {
    typing_env: TypingEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TermVisitorMut<'tcx> for NormalizeTerm<'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        super_visit_mut_term(term, self);
        match &mut term.kind {
            TermKind::Call { id, subst, args } => {
                if self.tcx.trait_of_item(*id).is_some() {
                    let method = TraitResolved::resolve_item(self.tcx, self.typing_env, *id, subst)
                        .to_opt(*id, subst)
                        .unwrap_or_else(|| {
                            panic!("could not resolve trait instance {:?}", (*id, *subst))
                        });
                    *id = method.0;
                    *subst = method.1;
                }

                if is_box_new(self.tcx, *id) {
                    let arg = args.remove(0);
                    *term = arg;
                    return;
                }

                if let Some(opt) = optimize_builtin(self.tcx, *id, args) {
                    term.kind = opt;
                }
            }
            TermKind::Item(id, subst) => {
                if self.tcx.trait_of_item(*id).is_some() {
                    let method = TraitResolved::resolve_item(self.tcx, self.typing_env, *id, subst)
                        .to_opt(*id, subst)
                        .unwrap_or_else(|| {
                            panic!("could not resolve trait instance {:?}", (*id, *subst))
                        });
                    *id = method.0;
                    *subst = method.1;
                }
            }
            _ => {}
        }
    }
}

fn optimize_builtin<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: &mut Vec<Term<'tcx>>,
) -> Option<TermKind<'tcx>> {
    Some(match get_builtin(tcx, def_id)?.as_str() {
        "add_int" => TermKind::Binary {
            op: BinOp::Add,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "sub_int" => TermKind::Binary {
            op: BinOp::Sub,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "mul_int" => TermKind::Binary {
            op: BinOp::Mul,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "div_int" => TermKind::Binary {
            op: BinOp::Div,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "rem_int" => TermKind::Binary {
            op: BinOp::Rem,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "neg_int" => TermKind::Unary { op: pearlite::UnOp::Neg, arg: Box::new(args.remove(0)) },
        "int.Int.(<=)" => TermKind::Binary {
            op: BinOp::Le,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "int.Int.(<)" => TermKind::Binary {
            op: BinOp::Lt,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "int.Int.(>=)" => TermKind::Binary {
            op: BinOp::Ge,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "int.Int.(>)" => TermKind::Binary {
            op: BinOp::Gt,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "==" => TermKind::Binary {
            op: BinOp::Eq,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "!=" => TermKind::Binary {
            op: BinOp::Ne,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        "creusot.int.UInt8$BW$.t'int"
            if let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.UInt16$BW$.t'int"
            if let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.UInt32$BW$.t'int"
            if let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.UInt64$BW$.t'int"
            if let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.UInt128$BW$.t'int"
            if let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind =>
        {
            if c > isize::MAX as u128 {
                return None;
            }
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.Int8$BW$.to_int"
            if let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.Int16$BW$.to_int"
            if let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.Int32$BW$.to_int"
            if let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.Int64$BW$.to_int"
            if let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "creusot.int.Int128$BW$.to_int"
            if let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind =>
        {
            TermKind::Lit(Literal::Integer(c as i128))
        }
        "identity" => args.remove(0).kind,
        _ => return None,
    })
}
