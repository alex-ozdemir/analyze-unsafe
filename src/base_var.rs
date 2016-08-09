// Alex Ozdemir <aozdemir@hmc.edu>
//
// Holds the `BaseVar`, a type that represents a simple location in MIR.
// It does not not divide product types into peices, or track references, like some path system
// might.


use rustc::mir::repr::{Arg,
                       Lvalue,
                       LvalueProjection,
                       Mir,
                       Operand,
                       ProjectionElem,
                       Rvalue,
                       Temp,
                       Terminator,
                       Var};

use rustc::hir::def_id::DefId;
use rustc::ty;

use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BaseVar {
    Var(Var),
    Temp(Temp),
    Arg(Arg),
    Static(DefId),
    ReturnPointer,
}

impl fmt::Debug for BaseVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BaseVar::Var(v) => write!(f, "{:?}", v),
            BaseVar::Temp(v) => write!(f, "{:?}", v),
            BaseVar::Arg(v) => write!(f, "{:?}", v),
            BaseVar::Static(v) => write!(f, "Static({:?})", v),
            BaseVar::ReturnPointer => write!(f, "ret"),
        }
    }
}

pub fn lvalue_to_var(lvalue: &Lvalue) -> BaseVar {
    use rustc::mir::repr::Lvalue::*;
    match *lvalue {
        Var(v) => BaseVar::Var(v),
        Temp(v) => BaseVar::Temp(v),
        Arg(v) => BaseVar::Arg(v),
        Static(v) => BaseVar::Static(v),
        ReturnPointer => BaseVar::ReturnPointer,
        Projection(box LvalueProjection { ref base, .. }) => lvalue_to_var(base),
    }
}

pub fn terminator_derefs_var(terminator: &Terminator, var: BaseVar) -> bool {
    use rustc::mir::repr::TerminatorKind::*;
    match terminator.kind {
        If{ cond: ref op, .. } |
        Assert{ cond: ref op, .. } => operand_derefs_var(op, var),

        DropAndReplace{ location: ref lval, value: ref op, .. } =>
            operand_derefs_var(op, var) || lvalue_derefs_var(lval, var),

        Switch{ discr: ref lval, .. } |
        SwitchInt{ discr: ref lval, .. } |
        Drop{ location: ref lval, .. } => lvalue_derefs_var(lval, var),

        Call { ref func, ref args, .. } =>
            operand_derefs_var(func, var) || args.iter().any(|op| operand_derefs_var(op, var)),
        Goto { .. } | Resume | Return | Unreachable => false,
    }
}

pub fn rvalue_derefs_var(rvalue: &Rvalue, var: BaseVar) -> bool {
    use rustc::mir::repr::Rvalue::*;
    match *rvalue {
        Use(ref operand) |
        Repeat(ref operand, _) |
        Cast(_, ref operand, _) |
        UnaryOp(_, ref operand) => operand_derefs_var(operand, var),

        BinaryOp(_, ref o1, ref o2) |
        CheckedBinaryOp(_, ref o1, ref o2) =>
            operand_derefs_var(o1, var) || operand_derefs_var(o2, var),

        Ref(_, _, ref lvalue) |
        Len(ref lvalue) => lvalue_derefs_var(lvalue, var),

        Aggregate(_, ref operands) => operands.iter().any(|o| operand_derefs_var(o, var)),
        InlineAsm { .. } => unimplemented!(),
        Box(_) => false,
    }
}

pub fn operand_derefs_var(operand: &Operand, var: BaseVar) -> bool {
    use rustc::mir::repr::Operand::*;
    match *operand {
        Consume(ref lvalue) => lvalue_derefs_var(lvalue, var),
        Constant(_) => false,
    }
}

pub fn lvalue_derefs_var(lvalue: &Lvalue, var: BaseVar) -> bool {
    match (lvalue, var) {
        (&Lvalue::Projection(box LvalueProjection { ref base, elem: ProjectionElem::Deref }),
            var) => lvalue_contains_var(base, var),
        (&Lvalue::Projection(box LvalueProjection { ref base, .. }), var) =>
            lvalue_derefs_var(base, var),
        _ => false,
    }
}

pub fn rvalue_contains_var(rvalue: &Rvalue, var: BaseVar) -> bool {
    use rustc::mir::repr::Rvalue::*;
    match *rvalue {
        Use(ref operand) |
        Repeat(ref operand, _) |
        Cast(_, ref operand, _) |
        UnaryOp(_, ref operand) => operand_contains_var(operand, var),

        BinaryOp(_, ref o1, ref o2) |
        CheckedBinaryOp(_, ref o1, ref o2) =>
            operand_contains_var(o1, var) || operand_contains_var(o2, var),

        Ref(_, _, ref lvalue) |
        Len(ref lvalue) => lvalue_contains_var(lvalue, var),

        Aggregate(_, ref operands) => operands.iter().any(|o| operand_contains_var(o, var)),
        InlineAsm { .. } => unimplemented!(),
        Box(_) => false,
    }
}

pub fn operand_contains_var(operand: &Operand, var: BaseVar) -> bool {
    use rustc::mir::repr::Operand::*;
    match *operand {
        Consume(ref lvalue) => lvalue_contains_var(lvalue, var),
        Constant(_) => false,
    }
}

pub fn lvalue_contains_var(lvalue: &Lvalue, var: BaseVar) -> bool {
    match (lvalue, var) {
        (&Lvalue::Var(ref v1), BaseVar::Var(v2)) => *v1 == v2,
        (&Lvalue::Temp(ref v1), BaseVar::Temp(v2)) => *v1 == v2,
        (&Lvalue::Arg(ref v1), BaseVar::Arg(v2)) => *v1 == v2,
        (&Lvalue::Static(ref v1), BaseVar::Static(v2)) => *v1 == v2,
        (&Lvalue::ReturnPointer, BaseVar::ReturnPointer) => true,
        (&Lvalue::Projection(box LvalueProjection { ref base, ref elem }), var) =>
            lvalue_contains_var(base, var) || match elem {
                &ProjectionElem::Index(ref operand) => operand_contains_var(operand, var),
                _ => false,
            },
        _ => false,
    }
}

pub fn rvalue_used_vars(rvalue: &Rvalue) -> Vec<BaseVar> {
    use rustc::mir::repr::Rvalue::*;
    match *rvalue {
        Use(ref operand) |
        Repeat(ref operand, _) |
        Cast(_, ref operand, _) |
        UnaryOp(_, ref operand) => operand_used_vars(operand),

        BinaryOp(_, ref o1, ref o2) |
        CheckedBinaryOp(_, ref o1, ref o2) => {
            let mut v = operand_used_vars(o1);
            v.extend(operand_used_vars(o2));
            v
        },

        Ref(_, _, ref lvalue) |
        Len(ref lvalue) => lvalue_used_vars(lvalue),

        Aggregate(_, ref operands) => {
            let mut v = vec![];
            operands.iter().map(|o| v.extend(operand_used_vars(o))).count();
            v
        },
        InlineAsm { .. } => unimplemented!(),
        Box(_) => vec![],
    }
}

pub fn operand_used_vars(operand: &Operand) -> Vec<BaseVar> {
    use rustc::mir::repr::Operand::*;
    match operand {
        &Consume(ref lvalue) => lvalue_used_vars(lvalue),
        //TODO: Is this correct?
        &Constant(_) => vec![],
    }
}

pub fn lvalue_used_vars(lvalue: &Lvalue) -> Vec<BaseVar> {
    match lvalue {
        &Lvalue::Var(ref v1) => vec![BaseVar::Var(*v1)],
        &Lvalue::Temp(ref v1) => vec![BaseVar::Temp(*v1)],
        &Lvalue::Arg(ref v1) => vec![BaseVar::Arg(*v1)],
        &Lvalue::Static(ref v1) => vec![BaseVar::Static(*v1)],
        &Lvalue::ReturnPointer => vec![BaseVar::ReturnPointer],
        &Lvalue::Projection(box LvalueProjection { ref base, ref elem }) => {
            let mut v = lvalue_used_vars(base);
            match elem {
                &ProjectionElem::Index(ref operand) => v.extend(operand_used_vars(operand)),
                _ => (),
            };
            v
        },
    }
}

pub fn rvalue_ptr_derefs<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                           tcx: ty::TyCtxt<'mir, 'gcx, 'tcx>,
                                           rvalue: &Rvalue<'tcx>)
                                           -> Vec<BaseVar> {
    use rustc::mir::repr::Rvalue::*;
    match *rvalue {
        Use(ref operand) |
        Repeat(ref operand, _) |
        Cast(_, ref operand, _) |
        UnaryOp(_, ref operand) => operand_ptr_derefs(mir, tcx, operand),

        BinaryOp(_, ref o1, ref o2) |
        CheckedBinaryOp(_, ref o1, ref o2) => {
            let mut v = operand_ptr_derefs(mir, tcx, o1);
            v.extend(operand_ptr_derefs(mir, tcx, o2));
            v
        }

        Ref(_, _, ref lvalue) |
        Len(ref lvalue) => lvalue_ptr_derefs(mir, tcx, lvalue),

        Aggregate(_, ref operands) => {
            let mut v = vec![];
            operands.iter().map(|o| v.extend(operand_ptr_derefs(mir, tcx, o))).count();
            v
        },
        InlineAsm { .. } => unimplemented!(),
        Box(_) => vec![],
    }
}

pub fn operand_ptr_derefs<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                            tcx: ty::TyCtxt<'mir, 'gcx, 'tcx>,
                                            operand: &Operand<'tcx>)
                                            -> Vec<BaseVar> {
    use rustc::mir::repr::Operand::*;
    match operand {
        &Consume(ref lvalue) => lvalue_ptr_derefs(mir, tcx, lvalue),
        //TODO: Is this correct?
        &Constant(_) => vec![],
    }
}

pub fn lvalue_ptr_derefs<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                           tcx: ty::TyCtxt<'mir, 'gcx, 'tcx>,
                                           lvalue: &Lvalue<'tcx>)
                                           -> Vec<BaseVar> {
    match lvalue {
        &Lvalue::Projection(box LvalueProjection { ref base, ref elem }) => {
            let mut v = lvalue_ptr_derefs(mir, tcx, base);
            match elem {
                &ProjectionElem::Deref => {
                    let base_ty = mir.lvalue_ty(tcx, base);
                    if let ty::TypeVariants::TyRawPtr(_) = base_ty.to_ty(tcx).sty {
                        v.extend(lvalue_used_vars(base));
                    }
                },
                &ProjectionElem::Index(ref operand) =>
                    v.extend(operand_ptr_derefs(mir, tcx, operand)),
                _ => (),
            };
            v
        },
        _ => vec![],
    }
}
