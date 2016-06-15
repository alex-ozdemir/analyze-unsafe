// Alex Ozdemir <aozdemri@hmc.edu>
// File for doing dataflow analysis on a CFG.

use rustc::mir::repr::{self,Arg,BasicBlock,Lvalue,LvalueProjection,Mir,Operand,ProjectionElem,Rvalue,START_BLOCK,Temp,Terminator,Var};
use rustc::mir::traversal;
use rustc::hir::def_id::DefId;
use rustc::ty;

use syntax::codemap::Span;

use std::collections::{HashSet,HashMap};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct StatementIdx(BasicBlock,usize);

const START: StatementIdx = StatementIdx(START_BLOCK,0);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum BaseVar {
    Var(Var),
    Temp(Temp),
    Arg(Arg),
    Static(DefId),
    ReturnPointer,
}

// Our facts are sets of Lvalues that are tainted
type Facts<'tcx> = HashSet<BaseVar>;

/// Analyzes a MIR, checks if an input raw pointer ever gets dereferenced.
/// Returns a vector containing all the problematic Spans - the locations of the dereference.
pub fn check_for_deref_of_unknown_ptr<'b,'tcx>(mir: &'b Mir<'tcx>) -> Vec<Span> {
    let mut tainted_vars: HashMap<StatementIdx,Facts<'tcx>> = HashMap::new();
    tainted_vars.insert(START, HashSet::new());

    for (id, arg) in mir.arg_decls.iter_enumerated() {
        match arg.ty.sty {
            ty::TypeVariants::TyRawPtr(_) => {
                tainted_vars.get_mut(&START).unwrap()
                            .insert(BaseVar::Arg(id));
            },
            _ => { /* No other types start tainted */ },
        };
    }

    let mut stable = false;
    while !stable {
        stable = true;
        for (bb_idx, basic_block) in traversal::reverse_postorder(mir) {

            // Push the taint through the statements that make the BB
            for (s_idx, statement) in basic_block.statements.iter().enumerate() {
                //println!("Working on BB {:?}, Stmt {:?}.", bb_idx, s_idx);

                let repr::StatementKind::Assign(ref lvalue, ref rvalue) = statement.kind;

                let old_stmnt_idx = StatementIdx(bb_idx, s_idx);
                let next_stmnt_idx = StatementIdx(bb_idx, s_idx + 1);

                // Taint for after the statement executes
                let mut next_taint = tainted_vars.remove(&next_stmnt_idx)
                                                 .unwrap_or(HashSet::new());

                // Is the value being assigned tainted?
                let tainted_inputs;
                {
                    // Taint for before the statement executes
                    let old_taint = tainted_vars.get(&old_stmnt_idx)
                                                .expect("rev-postorder");

                    // All originally tainted variables are still tainted.
                    for tainted_var in old_taint.iter() {
                        if !next_taint.contains(tainted_var) {
                            stable = false;
                            next_taint.insert(*tainted_var);
                        }
                    }

                    // The assigned variable is now tainted iff any inputs were tainted.
                    tainted_inputs = old_taint.iter()
                                              .any(|var| rvalue_contains_var(rvalue, *var));
                }

                if tainted_inputs {
                    let var = lvalue_to_var(lvalue);
                    if !next_taint.contains(&var) {
                        stable = false;
                        next_taint.insert(var);
                    }
                }
                // While technically a location assigned a non-tainted value is no longer tainted,
                // this can actually be ignored, because we start with all locations untainted, and
                // the taint analysis is a union over all paths.
                // Otherwise we'd remove the lvalue if the inputs weren't tainted.

                tainted_vars.insert(next_stmnt_idx, next_taint);
            }

            // Insert the taint into the next block(s)
            // Note: we only ever add taint to the next blocks, for the same reason as before
            let last_stmnt_idx = StatementIdx(bb_idx, basic_block.statements.len());

            for succ_bb_idx in basic_block.terminator().successors().iter() {
                let next_stmnt_idx = StatementIdx(*succ_bb_idx, 0);
                let mut next_taint = tainted_vars.remove(&next_stmnt_idx).unwrap_or(HashSet::new());

                // Pass along the tainted variables.
                for var in tainted_vars.get(&last_stmnt_idx).unwrap() {
                    if !next_taint.contains(var) {
                        stable = false;
                        next_taint.insert(*var);
                    }
                }

                tainted_vars.insert(next_stmnt_idx, next_taint);
            }

            // Also consider the case where the terminator makes an assignment (DropAndReplace,
            // Call). In these cases a new location is tainted.
            use rustc::mir::repr::TerminatorKind::{DropAndReplace,Call};
            let idx = StatementIdx(bb_idx, basic_block.statements.len());
            match basic_block.terminator().kind {
                DropAndReplace{ ref location, ref value, ref target, .. } =>
                    if tainted_vars.get(&idx).unwrap().iter()
                        .any(|var| operand_contains_var(value, *var)) {
                        let idx = &StatementIdx(*target, 0);
                        let var = lvalue_to_var(location);
                        if !tainted_vars.get(idx).unwrap().contains(&var) {
                            stable = false;
                            tainted_vars.get_mut(idx).unwrap().insert(var);
                        }
                    },
                Call{ destination: Some((ref lval, next_bb)), ref func, ref args, .. } => {
                    let tainted_args = tainted_vars.get(&idx).unwrap().iter()
                        .any(|var| args.iter().any(|arg| operand_contains_var(arg, *var)));
                    let tainted_fn = tainted_vars.get(&idx).unwrap().iter()
                        .any(|var| operand_contains_var(func, *var));
                    if tainted_args || tainted_fn {
                        let idx = &StatementIdx(next_bb, 0);
                        let var = lvalue_to_var(lval);
                        if !tainted_vars.get(idx).unwrap().contains(&var) {
                            stable = false;
                            tainted_vars.get_mut(idx).unwrap().insert(var);
                        }
                    }
                },
                _ => {/* Other terminators make no assignment */},
            }
        }
    }

    // Check if (and where) any tainted variables are dereferenced.
    let mut spans = vec![];
    for (bb_idx, basic_block) in traversal::reverse_postorder(mir) {

        // Check the statements
        for (s_idx, statement) in basic_block.statements.iter().enumerate() {
            let idx = StatementIdx(bb_idx, s_idx);
            let repr::StatementKind::Assign(_, ref rvalue) = statement.kind;
            for tainted_var in tainted_vars.get(&idx).unwrap() {
                if rvalue_derefs_var(rvalue, *tainted_var) {
                    spans.push(statement.source_info.span);
                }
            }
        }

        // Check the terminator
        let idx = StatementIdx(bb_idx, basic_block.statements.len());
        for tainted_var in tainted_vars.get(&idx).unwrap() {
            if terminator_derefs_var(basic_block.terminator(), *tainted_var) {
                spans.push(basic_block.terminator().source_info.span)
            }
        }
    }
    spans
}

fn lvalue_to_var(lvalue: &Lvalue) -> BaseVar {
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

fn terminator_derefs_var(terminator: &Terminator, var: BaseVar) -> bool {
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

fn rvalue_derefs_var(rvalue: &Rvalue, var: BaseVar) -> bool {
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

fn operand_derefs_var(operand: &Operand, var: BaseVar) -> bool {
    use rustc::mir::repr::Operand::*;
    match *operand {
        Consume(ref lvalue) => lvalue_derefs_var(lvalue, var),
        Constant(_) => false,
    }
}

fn lvalue_derefs_var(lvalue: &Lvalue, var: BaseVar) -> bool {
    match (lvalue, var) {
        (&Lvalue::Projection(box LvalueProjection { ref base, elem: ProjectionElem::Deref }),
            var) => lvalue_contains_var(base, var),
        (&Lvalue::Projection(box LvalueProjection { ref base, .. }), var) =>
            lvalue_derefs_var(base, var),
        _ => false,
    }
}

fn rvalue_contains_var(rvalue: &Rvalue, var: BaseVar) -> bool {
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

fn operand_contains_var(operand: &Operand, var: BaseVar) -> bool {
    use rustc::mir::repr::Operand::*;
    match *operand {
        Consume(ref lvalue) => lvalue_contains_var(lvalue, var),
        Constant(_) => false,
    }
}

fn lvalue_contains_var(lvalue: &Lvalue, var: BaseVar) -> bool {
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
