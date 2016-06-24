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

use path::*;

use base_var::BaseVar;

use syntax::ast::NodeId;

use std::collections::{BTreeSet,HashSet};

pub struct ComplexEscapeAnalysis;

impl BackwardsAnalysis for ComplexEscapeAnalysis {
    type Fact = Path;

    // The base variables which are made critical by this expression
    fn generate<'a, 'tcx>(expr: Expr<'a, 'tcx>) -> Vec<Self::Fact> {
        use backflow::Expr::*;
        match expr {
            Lvalue(ref lvalue) => assumed_valid_by_lvalue(lvalue),
            Rvalue(ref rvalue) => assumed_valid_by_rvalue(rvalue),
            Operand(ref operand) => assumed_valid_by_operand(operand),
        }
    }

    fn transfer<'tcx>(outs: &HashSet<Self::Fact>,
                      statement: &StatementKind<'tcx>)
                      -> HashSet<Self::Fact> {
        let &StatementKind::Assign(ref lval, ref rval) = statement;
        transfer_and_gen_paths_assign(outs, lval, rval)
    }
    fn join(many: Vec<&HashSet<Self::Fact>>) -> HashSet<Self::Fact> {
        let mut pre_facts = HashSet::new();
        many.iter().map(|facts|
                        facts.iter().map(|fact|
                                         pre_facts.insert(fact.clone())
                                        ).count()
                       ).count();
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
        fn_id.map_or_else(
        || {
            (None, HashSet::new())
        },
        |id| {
            let mut new_pre_facts = HashSet::new();
            let dest_path = lvalue_path(dest);
            new_pre_facts.extend(post_facts.iter().filter(|path| path.base != dest_path.base).cloned());
            let ret_path = Path::from_base_var(BaseVar::ReturnPointer);
            let return_facts: BTreeSet<_> = post_facts.iter()
                .filter_map(|path| path.substitute(&dest_path, &ret_path)).collect();
            let callee_cx = (id, return_facts);
            let args_and_paths =
                get_arg_paths(&callee_cx, crate_info, context_and_fn_to_fact_map);
            args_and_paths.into_iter().zip(arg_ops).map(|((arg_lval,paths),arg_ops)| {
                let arg_rval = Rvalue::Use(arg_ops.clone());
                new_pre_facts.extend(transfer_and_gen_paths_assign(&paths, &arg_lval, &arg_rval));
            }).count();
            new_pre_facts.extend(Self::generate(Expr::Operand(fn_op)));
            new_pre_facts.extend(Self::generate(Expr::Lvalue(dest)));
            (Some(callee_cx), new_pre_facts)
        })
        //TODO handle mysterious functions
        // Generate ...
    }
}

fn get_arg_paths<'mir,'tcx>(context: &FullCx<Path>,
                            crate_info: &CrateInfo<'mir,'tcx>,
                            context_and_fn_to_fact_map: &CrateFactsMap<Path>
    ) -> Vec<(Lvalue<'tcx>,HashSet<Path>)> {
    let empty = HashSet::new();
    let start_facts = context_and_fn_to_fact_map.get(context)
        .and_then(|m| m.get(&START_STMT)).unwrap_or(&empty);
    let ref arg_decls = crate_info.mir_map.map.get(&context.0).unwrap().arg_decls;
    arg_decls.indices().map(|arg_id| {
        let arg = BaseVar::Arg(arg_id);
        let arg_paths = start_facts.iter().filter(|path| path.base == arg).cloned().collect();
        (Lvalue::Arg(arg_id), arg_paths)

    }).collect()
}

impl<'mir,'tcx> AnalysisState<'mir,'tcx,BaseVar> {
    pub fn get_lints(&self,
                     analysis: &ty::CrateAnalysis,
                     hir: &hir::Crate)
                     -> Vec<(Span,String)> {
        let unsafe_fn_ids = get_unsafe_fn_ids(hir);
        analysis.access_levels.map.iter().filter(|&(id, _)|
            !unsafe_fn_ids.contains(id)
        ).filter_map(|(id, _)| {
            self.info.node_id_to_mir(id).and_then(|mir| {
                let start_facts = self.context_and_fn_to_fact_map
                    .get(&(*id, BTreeSet::new())).unwrap().get(&START_STMT).unwrap();
                let concerning_arguments: Vec<_> = start_facts.iter().filter_map(|var| {
                    match var {
                        &BaseVar::Arg(arg_idx) => Some(mir.arg_decls[arg_idx].debug_name),
                        _ => None,
                    }
                }).collect();
                if concerning_arguments.len() == 0 {
                    None
                } else {
                    let fn_name = self.info.tcx.item_path_str(self.info.tcx.map.local_def_id(*id));
                    let arguments: Vec<_>= concerning_arguments.iter().map(|name|
                        format!("`{}`", name)
                    ).collect();
                    let fmt_args = if arguments.len() > 1 {
                        format!("arguments {}", arguments.join(", "))
                    } else {
                        format!("argument {}", arguments[0])
                    };
                    let err_msg = format!("The publically visible function {} has critical {}. By inputting certain arguments a user of this function might cause an invalid raw pointer to be dereferenced", fn_name, fmt_args);
                    Some( (mir.span.clone(), err_msg) )
                }
            })
        }).collect()
    }
}
