// Alex Ozdemir <aozdemri@hmc.edu>
// File for doing dataflow analysis on a CFG.

use rustc::mir::repr::{self,BasicBlock,Mir,START_BLOCK};
use rustc::mir::traversal;
use rustc::ty;

use base_var::{BaseVar,
               lvalue_to_var,
               operand_contains_var,
               rvalue_derefs_var,
               terminator_derefs_var,
               rvalue_contains_var};

use syntax::codemap::Span;

use std::collections::{HashSet,HashMap};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct StatementIdx(BasicBlock,usize);

const START: StatementIdx = StatementIdx(START_BLOCK,0);

// Our facts are sets of Lvalues that are tainted
type Facts<'tcx> = HashSet<BaseVar>;

/// Analyzes a MIR, checks if an input raw pointer ever gets dereferenced.
/// Returns a vector containing all the problematic Spans - the locations of the dereference.
#[allow(dead_code)]
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
            // println!("{:?}", basic_block.terminator());
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
            let vars = tainted_vars.get(&idx).unwrap().iter().filter(|var| match var {
                &&BaseVar::Temp(_) => false,
                _ => true,
            });
            for tainted_var in vars {
                if rvalue_derefs_var(rvalue, *tainted_var) {
                    spans.push(statement.source_info.span);
                }
            }
        }

        // Check the terminator
        let idx = StatementIdx(bb_idx, basic_block.statements.len());
        let vars = tainted_vars.get(&idx).unwrap().iter().filter(|var| match var {
            &&BaseVar::Temp(_) => false,
            _ => true,
        });
        for tainted_var in vars {
            if terminator_derefs_var(basic_block.terminator(), *tainted_var) {
                spans.push(basic_block.terminator().source_info.span)
            }
        }
    }
    spans
}
