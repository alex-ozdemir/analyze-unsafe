pub struct SimpleEscapeAnalysis;

use back::{AnalysisState,
           BackwardsAnalysis,
           CrateInfo,
           CrateFactsMap,
           Expr,
           FullCx,
           get_unsafe_fn_ids,
           START_STMT,
};

use syntax::ast::NodeId;
use syntax::codemap::Span;

use rustc::hir;
use rustc_data_structures::indexed_vec::Idx;

use rustc::ty;

use rustc::mir::repr::{Lvalue,
                       Mir,
                       Operand,
                       StatementKind,
};

use base_var::{BaseVar,
               lvalue_to_var,
               lvalue_used_vars,
               operand_used_vars,
               rvalue_used_vars,
               lvalue_ptr_derefs,
               operand_ptr_derefs,
               rvalue_ptr_derefs,
};

use std::collections::{BTreeSet,HashSet};

impl SimpleEscapeAnalysis {
    // Maps an LValue to the BaseVar representing its location.
    fn location(lvalue: &Lvalue) -> BaseVar {
        lvalue_to_var(lvalue)
    }

    // The base variables which contribute to the value of this expression
    fn inputs(expr: Expr) -> Vec<BaseVar> {
        use back::Expr::*;
        match expr {
            Lvalue(ref lvalue) => lvalue_used_vars(lvalue),
            Rvalue(ref rvalue) => rvalue_used_vars(rvalue),
            Operand(ref operand) => operand_used_vars(operand),
        }
    }

    fn fact_to_input_idx(fact: BaseVar) -> Option<usize> {
        match fact {
            BaseVar::Arg(arg) => Some(arg.index()),
            _ => None,
        }
    }

    /// Simple heurestic for determining if a function call which uses a raw pointer is concerning.
    /// We say it is concerning if it is marked as 'unsafe' and takes a raw pointer.
    fn generate_fn_call<'tcx, 'mir>(mir_id: NodeId,
                                    crate_info: &CrateInfo<'mir, 'tcx>,
                                    fn_op: &Operand<'tcx>,
                                    arg_ops: &Vec<Operand<'tcx>>
                                    ) -> Vec<BaseVar> {
        use rustc::ty::TypeVariants::*;
        let def_id = crate_info.get_fn_def_id(fn_op);
        let mir = crate_info.mir_map.map.get(&mir_id).unwrap();
        let is_critical_use = match def_id {
            Some(def_id) => {
                if crate_info.get_fn_node_id(fn_op).is_none() {
                    match crate_info.tcx.lookup_item_type(def_id).ty.sty {
                        TyFnDef(_, _, ref bare_fn_ty) |
                        TyFnPtr(ref bare_fn_ty) =>
                            bare_fn_ty.unsafety == hir::Unsafety::Unsafe,
                        _ => bug!("Should be a function type!"),
                    }
                } else {
                    false
                }
            },
            None => true,
        };
        if is_critical_use {
            arg_ops.iter().flat_map(|arg_op|
                match mir.operand_ty(crate_info.tcx, arg_op).sty {
                    TyRawPtr(_) => operand_used_vars(arg_op).into_iter(),
                    _ => vec![].into_iter(),
                }
            ).collect()
        } else {
            vec![]
        }
    }
}

impl BackwardsAnalysis for SimpleEscapeAnalysis {
    type Fact = BaseVar;

    // The base variables which are made critical by this expression
    fn generate<'a, 'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                      tcx: ty::TyCtxt<'mir,'gcx,'tcx>,
                                      expr: Expr<'a, 'tcx>) -> Vec<BaseVar> {
        use back::Expr::*;
        match expr {
            Lvalue(ref lvalue) => lvalue_ptr_derefs(mir, tcx, lvalue),
            Rvalue(ref rvalue) => rvalue_ptr_derefs(mir, tcx, rvalue),
            Operand(ref operand) => operand_ptr_derefs(mir, tcx, operand),
        }
    }

    fn transfer<'mir,'gcx,'tcx>(mir: &Mir<'tcx>,
                           tcx: ty::TyCtxt<'mir,'gcx,'tcx>,
                           outs: &HashSet<Self::Fact>,
                           statement: &StatementKind<'tcx>)
                           -> HashSet<Self::Fact> {
        let mut pre_facts = HashSet::new();
        let &StatementKind::Assign(ref lval, ref rval) = statement;
        outs.iter().map(|fact| pre_facts.insert(*fact)).count();

        let location = SimpleEscapeAnalysis::location(lval);
        pre_facts.remove(&location);

        if outs.contains(&location) {
            pre_facts.extend(SimpleEscapeAnalysis::inputs(Expr::Rvalue(rval)));
        }

        pre_facts.extend(SimpleEscapeAnalysis::generate(mir, tcx, Expr::Lvalue(lval)));
        pre_facts.extend(SimpleEscapeAnalysis::generate(mir, tcx, Expr::Rvalue(rval)));
        pre_facts
    }
    fn join(many: Vec<&HashSet<Self::Fact>>) -> HashSet<Self::Fact> {
        let mut pre_facts = HashSet::new();
        many.iter().map(|facts|
                        facts.iter().map(|fact|
                                         pre_facts.insert(*fact)
                                        ).count()
                       ).count();
        pre_facts
    }
    //TODO(aozdemir) handle diverging fn's properly
    fn fn_call_transfer<'mir,'tcx>(mir_id: NodeId,
                                   crate_info: &CrateInfo<'mir,'tcx>,
                                   context_and_fn_to_fact_map: &CrateFactsMap<Self::Fact>,
                                   post_facts: &HashSet<Self::Fact>,
                                   fn_op: &Operand<'tcx>,
                                   arg_ops: &Vec<Operand<'tcx>>,
                                   dest: &Lvalue<'tcx>)
                                   -> (Option<FullCx<Self::Fact>>, HashSet<Self::Fact>) {
        let mut new_pre_facts = HashSet::new();
        new_pre_facts.extend(post_facts);

        let location = Self::location(dest);
        new_pre_facts.remove(&location);

        let fn_id = crate_info.get_fn_node_id(fn_op);
        let result_is_critical = post_facts.contains(&location);
        let mut call_context = BTreeSet::new();
        if result_is_critical { call_context.insert(BaseVar::ReturnPointer); }
        let critical_indices = fn_id.map_or_else(|| {
            (0..arg_ops.len()).collect::<Vec<_>>()
        }, |id| {
            let callee_fact_map = context_and_fn_to_fact_map.get(&(id, call_context.clone()));
            let tmp = HashSet::new();
            let callee_start_facts = callee_fact_map
                .and_then(|m| m.get(&START_STMT)).unwrap_or(&tmp);
            let mut indices = callee_start_facts.iter().filter_map(
                |fact| Self::fact_to_input_idx(*fact)
            ).collect::<Vec<_>>();
            indices.sort();
            indices
        });
        if result_is_critical || fn_id.is_some() {
            for arg_idx in critical_indices.iter() {
                new_pre_facts.extend(Self::inputs(Expr::Operand(&arg_ops[*arg_idx])));
            }
        }

        // Generate ...
        let mir = crate_info.node_id_to_mir(&mir_id).unwrap();
        for arg_op in arg_ops {
            new_pre_facts.extend(Self::generate(mir, crate_info.tcx, Expr::Operand(arg_op)));
        }
        new_pre_facts.extend(Self::generate(mir, crate_info.tcx, Expr::Operand(fn_op)));
        new_pre_facts.extend(Self::generate(mir, crate_info.tcx, Expr::Lvalue(dest)));

        // Generate from mysterious function call. That is, if we pass raw pointers into some
        // unsafe unknown function, the argument pass is take to be critical.
        new_pre_facts.extend(Self::generate_fn_call(mir_id, crate_info, fn_op, arg_ops));
        (fn_id.map(|id| (id, call_context.clone())), new_pre_facts)
    }
}

impl<'mir,'tcx> AnalysisState<'mir,'tcx,BaseVar> {
    #[allow(dead_code)]
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

