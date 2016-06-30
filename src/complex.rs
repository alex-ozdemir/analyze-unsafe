use backflow::{BackwardsAnalysis,
               CrateInfo,
               CrateFactsMap,
               Expr,
               FullCx,
               get_unsafe_fn_ids,
               START_STMT,
};

use rustc::mir::repr::{Lvalue,
                       Rvalue,
                       Operand,
                       StatementKind,
};

use rustc::hir;
use rustc::ty::{self, TypeVariants};

use path::*;

use base_var::BaseVar;

use syntax::ast::NodeId;
use syntax::codemap::Span;

use backflow::AnalysisState;

use std::collections::{BTreeSet,HashSet};

pub struct ComplexEscapeAnalysis;

impl BackwardsAnalysis for ComplexEscapeAnalysis {
    type Fact = CriticalPath;

    // The base variables which are made critical by this expression
    fn generate<'a, 'tcx, 'mir>(
        mir_id: NodeId,
        crate_info: &CrateInfo<'mir,'tcx>,
        expr: Expr<'a, 'tcx>
        ) -> Vec<Self::Fact> {
        use backflow::Expr::*;
        let mir = crate_info.node_id_to_mir(&mir_id).unwrap();
        match expr {
            Lvalue(ref lvalue) => gen_by_lvalue(mir, crate_info.tcx, lvalue),
            Rvalue(ref rvalue) => gen_by_rvalue(mir, crate_info.tcx, rvalue),
            Operand(ref operand) => gen_by_operand(mir, crate_info.tcx, operand),
        }
    }

    fn transfer<'tcx,'mir>(mir_id: NodeId,
                           crate_info: &CrateInfo<'mir,'tcx>,
                           outs: &HashSet<Self::Fact>,
                           lvalue: &Lvalue<'tcx>,
                           rvalue: &Rvalue<'tcx>)
                           -> HashSet<Self::Fact> {
        let mir = crate_info.node_id_to_mir(&mir_id).unwrap();
        let mut transfered = just_sub_paths(mir, crate_info.tcx, outs, lvalue, rvalue);
        transfered.extend(gen_by_lvalue(mir, crate_info.tcx, lvalue));
        transfered.extend(gen_by_rvalue(mir, crate_info.tcx, rvalue));
        transfered
    }

    fn join(many: Vec<&HashSet<Self::Fact>>) -> HashSet<Self::Fact> {
        let mut pre_facts = HashSet::new();
        for fact_set in many {
            for fact in fact_set {
                pre_facts.insert(fact.clone());
            }
        }
        pre_facts
    }

    fn fn_call_transfer<'mir,'tcx>(mir_id: NodeId,
                                   crate_info: &CrateInfo<'mir,'tcx>,
                                   context_and_fn_to_fact_map: &CrateFactsMap<Self::Fact>,
                                   post_facts: &HashSet<Self::Fact>,
                                   fn_op: &Operand<'tcx>,
                                   arg_ops: &Vec<Operand<'tcx>>,
                                   dest: &Lvalue<'tcx>)
                                   -> (Option<FullCx<Self::Fact>>, HashSet<Self::Fact>) {

        let fn_id = crate_info.get_fn_node_id(fn_op);

        let mut new_pre_facts = HashSet::new();

        // Do `dest = ret`, where `ret` stands in for the return of the callee.
        // Split the resulting facts by whether they involve the return.
        let ret_ptr = Rvalue::Use(Operand::Consume(Lvalue::ReturnPointer));
        let (facts_at_end_of_callee, dont_involve_ret): (HashSet<_>,_) =
            Self::transfer(mir_id, crate_info, post_facts, dest, &ret_ptr).into_iter()
                .partition(|p| p.of_return_pointer());

        // Facts uninvolved with the return flow around the fn-call.
        new_pre_facts.extend(dont_involve_ret.into_iter());

        match fn_id {
            None => {
                let def_id = crate_info.get_fn_def_id(fn_op);
                let mir = crate_info.mir_map.map.get(&mir_id).unwrap();
                let is_unsafe = match def_id {
                    Some(def_id) => {
                        if crate_info.get_fn_node_id(fn_op).is_none() {
                            match crate_info.tcx.lookup_item_type(def_id).ty.sty {
                                TypeVariants::TyFnDef(_, _, ref bare_fn_ty) |
                                TypeVariants::TyFnPtr(ref bare_fn_ty) =>
                                    bare_fn_ty.unsafety == hir::Unsafety::Unsafe,
                                _ => bug!("Should be a function type!"),
                            }
                        } else {
                            false
                        }
                    },
                    // None means it's a closure, treat it as unsafe.
                    // TODO: I think this is the only sound option, but it is quite imprecise
                    None => true,
                };
                let l_path = lvalue_path(dest);
                let critical_return = facts_at_end_of_callee.len() > 0;

                // Generate any facts from evaluating actual arguments
                arg_ops.iter().map(|op|
                    new_pre_facts.extend(Self::generate(mir_id, crate_info, Expr::Operand(op)))
                ).count();

                // If unsafe or critical return, declare the all actual arguments value-critical
                if is_unsafe || critical_return {
                    new_pre_facts.extend(arg_ops.iter().filter_map(|op| operand_path(op).map(CriticalPath::value)))
                }
                (None, new_pre_facts)
            },
            Some(id) => {
                // Determine the analysis unit for the callee.
                let callee_analysis_unit = (id, facts_at_end_of_callee.into_iter().collect());

                // Lookup the facts for the AU's formal arguments.
                let args_and_paths =
                    get_arg_paths(&callee_analysis_unit, crate_info, context_and_fn_to_fact_map);

                // Assign the actual arguments to the formal ones.
                args_and_paths.into_iter().zip(arg_ops).map(|((arg_lval,paths),arg_ops)| {
                    let arg_rval = Rvalue::Use(arg_ops.clone());
                    new_pre_facts.extend(
                        Self::transfer(mir_id, crate_info, &paths, &arg_lval, &arg_rval)
                    )
                }).count();

                // Verify that the fn_op didn't produce any facts, nor did the ret_ptr
                debug_assert_eq!(0,
                                 Self::generate(mir_id, crate_info, Expr::Operand(fn_op)).len());
                debug_assert_eq!(0,
                                 Self::generate(mir_id, crate_info, Expr::Rvalue(&ret_ptr)).len());

                (Some(callee_analysis_unit), new_pre_facts)
            }
        }
        //TODO handle mysterious functions
        // Generate ...
    }
}

fn get_arg_paths<'mir,'tcx>(context: &FullCx<CriticalPath>,
                            crate_info: &CrateInfo<'mir,'tcx>,
                            context_and_fn_to_fact_map: &CrateFactsMap<CriticalPath>
    ) -> Vec<(Lvalue<'tcx>,HashSet<CriticalPath>)> {
    let empty = HashSet::new();
    let start_facts = context_and_fn_to_fact_map.get(context)
        .and_then(|m| m.get(&START_STMT)).unwrap_or(&empty);
    let ref arg_decls = crate_info.mir_map.map.get(&context.0).unwrap().arg_decls;
    arg_decls.indices().map(|arg_id| {
        let arg = BaseVar::Arg(arg_id);
        let arg_paths = start_facts.iter().filter(|path| *path.base() == arg).cloned().collect();
        (Lvalue::Arg(arg_id), arg_paths)

    }).collect()
}

impl<'mir,'tcx> AnalysisState<'mir,'tcx,CriticalPath> {

    /// Produces a list of (Span, Error Message) pairs.
    pub fn get_lints(&self,
                     analysis: &ty::CrateAnalysis,
                     hir: &hir::Crate)
                     -> Vec<(Span,String)> {

        // Get a list of ids for the unsafe functions (TODO there's got to be a better way)
        let unsafe_fn_ids = get_unsafe_fn_ids(hir);
        // Look through all safe exports
        analysis.access_levels.map.iter().filter(|&(id, _)|
            !unsafe_fn_ids.contains(id)
        ).filter_map(|(id, _)| {
            self.info.node_id_to_mir(id).and_then(|mir| {
                let start_facts = self.context_and_fn_to_fact_map
                    .get(&(*id, BTreeSet::new())).unwrap().get(&START_STMT).unwrap();
                let concerning_paths: Vec<_> = start_facts.iter().filter_map(|path| {
//                    match path.base_var() {
//                        BaseVar::Arg(_) => {
//                            let arg_str = mir.arg_decls[arg_dx].debug_name;
//                            Some(format!("{}", path
//                        }
//                    }
                    if path.of_argument() {
                        Some(format!("{}", path))
                    } else { None }
                }).collect();
                if concerning_paths.len() == 0 {
                    None
                } else {
                    let fn_name = self.info.tcx.item_path_str(self.info.tcx.map.local_def_id(*id));
                    let arguments: Vec<_>= concerning_paths.iter().map(|name|
                        format!("`{}`", name)
                    ).collect();
                    let fmt_args = if arguments.len() > 1 {
                        format!("arguments {}", arguments.join(", "))
                    } else {
                        format!("argument {}", arguments[0])
                    };
                    let err_msg = format!("The publically visible function `{}` has critical {}. By inputting certain arguments a user of this function might cause an invalid raw pointer to be dereferenced", fn_name, fmt_args);
                    Some( (mir.span.clone(), err_msg) )
                }
            })
        }).collect()
    }
}
