use backflow::{BackwardsAnalysis,
               CrateInfo,
               CrateFactsMap,
               Expr,
               get_unsafe_fn_ids,
               MIRInfo,
               START_STMT,
};

use rustc::mir::repr::{Lvalue,
                       Rvalue,
                       Operand,
                       StatementKind,
                       Var,
};

use rustc::hir;
use rustc::ty::{self, TypeVariants};

use path::Path;

use transfer::{transfer,
               join,
               operand_path,
               lvalue_path,
               gen_by_lvalue,
               gen_by_rvalue,
               gen_by_operand,
               Facts,
               CriticalUse,
};

use base_var::BaseVar;

use syntax::ast::NodeId;
use syntax::codemap::Span;

use backflow::{
    AnalysisState,
    AnalysisUnit,
};

use std::collections::{BTreeSet,HashSet};

use std::io::Write;
macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

pub struct ComplexEscapeAnalysis;

impl BackwardsAnalysis for ComplexEscapeAnalysis {
    type Facts = Facts;

    // The base variables which are made critical by this expression
    fn generate<'a, 'b, 'tcx: 'a + 'b + 'mir, 'mir, 'gcx: 'tcx>(
        mir_info: MIRInfo<'b, 'mir, 'gcx, 'tcx>,
        expr: Expr<'a, 'tcx>
        ) -> Self::Facts {
        use backflow::Expr::*;
        match expr {
            Lvalue(ref lvalue) => gen_by_lvalue(mir_info, lvalue),
            Rvalue(ref rvalue) => gen_by_rvalue(mir_info, rvalue),
            Operand(ref operand) => gen_by_operand(mir_info, operand),
        }
    }

    fn transfer<'a,'mir,'tcx:'a,'gcx:'tcx>(mir_info: MIRInfo<'a,'mir,'gcx,'tcx>,
                                           post_facts: &Self::Facts,
                                           statement: &StatementKind<'tcx>)
                                           -> Self::Facts {
        transfer(mir_info, statement, post_facts)
    }

    fn join(left: &Self::Facts, right: &Self::Facts) -> Self::Facts {
        join(left, right)
    }
    fn fn_call_transfer<'mir,'tcx>(mir_id: NodeId,
                                   crate_info: &CrateInfo<'mir,'tcx>,
                                   context_and_fn_to_fact_map: &CrateFactsMap<Self::Facts>,
                                   post_facts: &Self::Facts,
                                   fn_op: &Operand<'tcx>,
                                   arg_ops: &Vec<Operand<'tcx>>,
                                   dest: &Lvalue<'tcx>)
                                   -> (Option<AnalysisUnit<Self::Facts>>, Self::Facts) {

        let fn_id = crate_info.get_fn_node_id(fn_op);
        let mir_info = crate_info.get_mir_info(&mir_id);

        let mut new_pre_facts = Facts::empty();

        // Do `dest = ret`, where `ret` stands in for the return of the callee.
        // Split the resulting facts by whether they involve the return.
        // We use an intermediate
        let fresh_var: Var  = mir_info.fresh_var();
        let fresh_base_var = BaseVar::Var(fresh_var.clone());
        let ret_rvalue = Rvalue::Use(Operand::Consume(Lvalue::Var(fresh_var)));
        let assign_from_ret = StatementKind::Assign(dest.clone(),ret_rvalue.clone());

        let callee_info = crate_info.get_mir_info(&mir_id);
        let (mut facts_at_end_of_callee, dont_involve_ret): (Self::Facts,_) =
            Self::transfer(callee_info, post_facts, &assign_from_ret).into_iter()
                .partition(|&(ref p,_)| p.has_base_var(&fresh_base_var));

        let facts_at_end_of_callee: Facts = facts_at_end_of_callee.into_iter().map(|(mut p, u)| {
            p.change_base_var(BaseVar::ReturnPointer);
            (p, u)
        }).collect();

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
                for op in arg_ops {
                    new_pre_facts.extend(Self::generate(mir_info, Expr::Operand(op)))
                }

                // If unsafe or critical return, declare the all actual arguments value-critical
                if is_unsafe || critical_return {
                    new_pre_facts.extend(arg_ops.iter().filter_map(|op| {
                        operand_path(op).map(|p| (p, CriticalUse::Value))
                    }))
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
                        Self::transfer(mir_info, &paths, &StatementKind::Assign(arg_lval,arg_rval))
                    )
                }).count();

                // Verify that the fn_op didn't produce any facts, nor did the ret_ptr
                debug_assert_eq!(0, Self::generate(mir_info, Expr::Operand(fn_op)).len());
                debug_assert_eq!(0, Self::generate(mir_info, Expr::Rvalue(&ret_rvalue)).len());

                (Some(callee_analysis_unit), new_pre_facts)
            }
        }
        //TODO handle mysterious functions
        // Generate ...
    }

}

fn get_arg_paths<'mir,'tcx>(context: &AnalysisUnit<Facts>,
                            crate_info: &CrateInfo<'mir,'tcx>,
                            context_and_fn_to_fact_map: &CrateFactsMap<Facts>
    ) -> Vec<(Lvalue<'tcx>,Facts)> {
    let empty = Facts::empty();
    let start_facts = context_and_fn_to_fact_map.get(context)
        .and_then(|m| m.get(&START_STMT)).unwrap_or(&empty);
    let ref arg_decls = crate_info.mir_map.map.get(&context.0).unwrap().arg_decls;
    arg_decls.indices().map(|arg_id| {
        let arg = BaseVar::Arg(arg_id);
        let arg_facts = start_facts.iter()
            .filter(|&(path, u)| path.has_base_var(&arg))
            .map(|(path,u)| (path.clone(), u.clone())).collect();
        (Lvalue::Arg(arg_id), arg_facts)

    }).collect()
}

impl<'mir,'tcx> AnalysisState<'mir,'tcx,Facts> {

    /// Produces a list of (Span, Error Message) pairs.
    pub fn get_lints(&self,
                     analysis: &ty::CrateAnalysis,
                     hir: &hir::Crate)
                     -> Vec<(Span,String)> {
        errln!("Hi from linter!");
        // Get a list of ids for the unsafe functions (TODO there's got to be a better way)
        let unsafe_fn_ids = get_unsafe_fn_ids(hir);
        // Look through all safe exports
        analysis.access_levels.map.iter().filter(|&(id, _)|
            !unsafe_fn_ids.contains(id)
        ).filter_map(|(id, _)| {
            errln!("Fn: {}", id);
            self.info.node_id_to_mir(id).and_then(|mir| {
                let start_facts: &Facts = self.context_and_fn_to_fact_map
                    .get(&(*id, Facts::empty())).unwrap().get(&START_STMT).unwrap();
                let concerning_paths: Vec<_> = start_facts.iter().filter_map(|(path, u)| {
                    errln!("  - {}", path);
                    if path.of_argument() {
                        Some(format!("{:?}", path))
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
