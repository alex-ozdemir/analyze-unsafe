use backflow::{AnalysisUnit,
               BackwardsAnalysis,
               CrateInfo,
               CrateFactsMap,
               Expr,
               Context,
               Facts,
               get_unsafe_fn_ids,
               MIRInfo,
               START_STMT,
};

use rustc::mir::repr::{Lvalue,
                       Rvalue,
                       Operand,
                       StatementKind,
                       Var,
                       Arg,
};

use rustc_data_structures::indexed_vec::Idx;
use rustc::hir::def_id::DefId;
use rustc::hir::map as hir_map;

use rustc::hir;
use rustc::ty;

use path::{Path,paths_to_field_acc,Projectable};

use transfer::{transfer,
               join,
               operand_path,
               gen_by_lvalue,
               gen_by_rvalue,
               gen_by_operand,
               CriticalPaths,
               CriticalUse,
};

use base_var::{BaseVar,lvalue_to_var};

use syntax::ast::NodeId;
use syntax::codemap::Span;
use syntax::abi;

use backflow::{
    AnalysisState,
    RawAnalysisUnit,
};

use std::fmt::Debug;

use std::io::Write;
macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

pub struct ComplexEscapeAnalysis;

impl<Base: Clone + Ord + Debug> Facts for CriticalPaths<Base> {
    fn join(&self, right: &Self) -> Self {
        join(self, right)
    }
}

impl ComplexEscapeAnalysis {
    fn fn_call_mir_ids<'mir,'tcx>(
        caller_did: DefId,
        callee_did: Option<DefId>,
        fn_ty: &'tcx ty::BareFnTy<'tcx>,
        crate_info: &CrateInfo<'mir,'tcx>,
        context_and_fn_to_fact_map: &CrateFactsMap<CriticalPaths<BaseVar>>,
        post_facts: &CriticalPaths<BaseVar>,
        arg_ops: &Vec<Operand<'tcx>>,
        dest: &Lvalue<'tcx>)
        -> (Option<RawAnalysisUnit<CriticalPaths<BaseVar>>>, CriticalPaths<BaseVar>)
    {
        let mut caller_info = crate_info.get_mir_info(&caller_did);

        let mut new_pre_facts = CriticalPaths::empty();

        // Do `dest = ret`, where `ret` stands in for the return of the callee.
        // Split the resulting facts by whether they involve the return.
        // We use an intermediate
        let fresh_var: Var  = caller_info.fresh_var();
        let fresh_base_var = BaseVar::Var(fresh_var.clone());
        let ret_rvalue = Rvalue::Use(Operand::Consume(Lvalue::Var(fresh_var)));
        let assign_from_ret = StatementKind::Assign(dest.clone(),ret_rvalue.clone());

        let (facts_at_end_of_callee, dont_involve_ret): (CriticalPaths<BaseVar>,_) =
            Self::transfer(caller_info, post_facts, &assign_from_ret).into_iter()
                .partition(|&(ref p,_)| p.has_base(&fresh_base_var));

        let facts_at_end_of_callee: CriticalPaths<BaseVar> =
            facts_at_end_of_callee.into_iter().map(|(mut p, u)| {
                p.change_base(BaseVar::ReturnPointer);
                (p, u)
            }).collect();

        // CriticalPaths uninvolved with the return flow around the fn-call.
        new_pre_facts.extend(dont_involve_ret.into_iter());
        errln!("  Fn: {:?}", callee_did);
        match callee_did {
            Some(id) if id.is_local() => {
                // Determine the analysis unit for the callee.
                let raw_context = facts_at_end_of_callee.into_iter().collect();
                let callee_analysis_unit = (id, raw_context);

                // Lookup the facts for the AU's formal arguments.
                let mut args_and_paths =
                    get_arg_paths(&callee_analysis_unit, crate_info, context_and_fn_to_fact_map);

                // Assign the actual arguments to the formal ones.
                match fn_ty.abi {
                    abi::Abi::Rust => {
                        // Arguments / Paths already in the correct format.
                    },
                    abi::Abi::RustCall => {
                        // In the RustCall Abi the first actual argument is the receiver and the
                        // second is a tuple of arguments. However, for the formal parameters the
                        // first argument is the reciever and the 2nd through nth are the rest of
                        // the arguments (the tuple is split).
                        debug_assert_eq!(2, arg_ops.len());
                        let mut args_and_paths_i = args_and_paths.into_iter();
                        let receiver_arg_and_paths = args_and_paths_i.next()
                                                                     .expect("Must be a 1st arg");
                        // Replace the rest of the paths with extensions of the tuple
                        let tuple_arg = Lvalue::Arg(Arg::new(1));
                        let mut tuple_paths = CriticalPaths::empty();
                        args_and_paths_i.enumerate().map(|(i, (arg_id, mut paths))| {
                            let tuple_field =
                                Path::from_base(BaseVar::Arg(Arg::new(1))).tuple_field(i);
                            paths.replace_base(&lvalue_to_var(&arg_id), tuple_field);
                            tuple_paths.extend(paths);
                        }).count();
                        args_and_paths = vec![receiver_arg_and_paths, (tuple_arg, tuple_paths)];
                    },
                    _ => bug!("How do we even have a MIR if it's not rust?!"),
                }
                args_and_paths.into_iter().zip(arg_ops).map(|((_,paths),arg_op)| {
                    let arg_rval = Rvalue::Use(arg_op.clone());
                    let tmp_arg_id = caller_info.fresh_var();
                    let tmp_arg_base_var = BaseVar::Var(tmp_arg_id);
                    let tmp_arg_lval = Lvalue::Var(tmp_arg_id);
                    let externed_paths = paths.into_iter().map(|(mut p, u)| {
                        p.change_base(tmp_arg_base_var);
                        (p, u)
                    }).collect();
                    let assignment = StatementKind::Assign(tmp_arg_lval,arg_rval);
                    caller_info.set_optimistic_alias(true);
                    let transferred_paths = Self::transfer(caller_info, &externed_paths, &assignment);
                    caller_info.set_optimistic_alias(false);
                    let re_interned_paths = transferred_paths.into_iter().filter(|&(ref p, _)|
                        !p.has_base(&tmp_arg_base_var)
                    );
                    new_pre_facts.extend(re_interned_paths)
                }).count();

                // Verify that the fn_op didn't produce any facts, nor did the ret_ptr
                debug_assert_eq!(0, Self::generate(caller_info, Expr::Rvalue(&ret_rvalue)).len());

                (Some(callee_analysis_unit), new_pre_facts)
            }
            _ => {
                let is_unsafe = fn_ty.unsafety == hir::Unsafety::Unsafe;
                let critical_return = facts_at_end_of_callee.len() > 0;

                // Generate any facts from evaluating actual arguments
                for op in arg_ops {
                    new_pre_facts.extend(Self::generate(caller_info, Expr::Operand(op)))
                }

                // If unsafe or critical return, declare the all actual arguments value-critical
                if is_unsafe || critical_return {
                    new_pre_facts.extend(arg_ops.iter().filter_map(|op| {
                        operand_path(op).map(|p| (p, CriticalUse::Value))
                    }))
                }
                (None, new_pre_facts)
            },
        }
    }

}

impl BackwardsAnalysis for ComplexEscapeAnalysis {
    type Facts = CriticalPaths<BaseVar>;
    type GlobalFacts = CriticalPaths<DefId>;

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

    fn substantiate_au<'mir,'tcx>(
        state: &mut AnalysisState<Self::Facts,Self::GlobalFacts>,
        (fn_nid, cx): AnalysisUnit<Self::Facts>
    ) -> RawAnalysisUnit<Self::Facts> {
        match cx {
            Context::User => {
                let mut critical_paths = CriticalPaths::empty();
                for (ref field_path, ref criticalness) in state.user_cx.iter() {
                    let mir_info = state.info.get_mir_info(&fn_nid);
                    for mut path_to_field in paths_to_field(mir_info, field_path.base().clone()) {
                        path_to_field.extend_in_place(field_path.as_extension());
                        critical_paths.insert(path_to_field, (*criticalness).clone())
                    }
                }
                (fn_nid, critical_paths)
            },
            Context::Internal(critical_paths) => (fn_nid, critical_paths),
        }
    }

    fn fn_call_transfer<'mir,'tcx>(caller_did: DefId,
                                   crate_info: &CrateInfo<'mir,'tcx>,
                                   context_and_fn_to_fact_map: &CrateFactsMap<Self::Facts>,
                                   post_facts: &Self::Facts,
                                   fn_op: &Operand<'tcx>,
                                   arg_ops: &Vec<Operand<'tcx>>,
                                   dest: &Lvalue<'tcx>)
                                   -> (Option<RawAnalysisUnit<Self::Facts>>, Self::Facts) {

        let callee_did = crate_info.get_fn_def_id(fn_op);
        let fn_ty = crate_info.get_fn_ty(&caller_did, fn_op);
        Self::fn_call_mir_ids(caller_did, callee_did, fn_ty, crate_info, context_and_fn_to_fact_map, post_facts, arg_ops, dest)
    }

    fn extract_global_facts<'a, 'mir, 'gcx: 'tcx, 'tcx: 'mir + 'a>(
        entry_facts: &Self::Facts,
        mir_info: MIRInfo<'a, 'mir, 'tcx, 'gcx>
    ) -> Self::GlobalFacts {
        let mut paths = CriticalPaths::empty();
        for (path, criticalness) in entry_facts.iter() {
            if path.may_escape() {
                if let Some(field_path) = mir_info.path_from_private(path.as_ref()) {
                    paths.insert(field_path, criticalness.clone());
                }
            }
        }
        paths
    }

}

fn get_arg_paths<'mir,'tcx>(raw_au: &RawAnalysisUnit<CriticalPaths<BaseVar>>,
                            crate_info: &CrateInfo<'mir,'tcx>,
                            context_and_fn_to_fact_map: &CrateFactsMap<CriticalPaths<BaseVar>>
    ) -> Vec<(Lvalue<'tcx>,CriticalPaths<BaseVar>)> {
    errln!("    Lookup: {:?}", raw_au);
    let au = (raw_au.0.clone(), Context::Internal(raw_au.1.clone()));
    let empty = CriticalPaths::empty();
    let start_facts = context_and_fn_to_fact_map.get(&au)
        .and_then(|m| m.get(&START_STMT)).unwrap_or(&empty);
    let ref arg_decls = crate_info.mir_map.map.get(&raw_au.0).unwrap().arg_decls;
    arg_decls.indices().map(|arg_id| {
        let arg = BaseVar::Arg(arg_id);
        let arg_facts = start_facts.iter()
            .filter(|&(path, _)| path.has_base(&arg))
            .map(|(path,u)| (path.clone(), u.clone())).collect();
        (Lvalue::Arg(arg_id), arg_facts)

    }).collect()
}

impl<'mir,'tcx> AnalysisState<'mir,'tcx,CriticalPaths<BaseVar>,CriticalPaths<DefId>> {

    /// Produces a list of (Span, Error Message) pairs.
    pub fn get_lints<'ast>(&self,
                           hir: &hir::Crate)
                           -> Vec<(Span,String)> {
        // Get a list of ids for the unsafe functions (TODO there's got to be a better way)
        let unsafe_fn_ids = get_unsafe_fn_ids(hir);
        // Look through all safe exports
        self.info.analysis.access_levels.map.iter().filter(|&(id, _)|
            !unsafe_fn_ids.contains(id)
        ).filter_map(|(fn_nid, _)| {
            if let Some(fn_did) = self.info.tcx.map.opt_local_def_id(*fn_nid) {
                self.info.did_to_mir(&fn_did).and_then(|mir| {
                    let mir_info = self.info.get_mir_info(&fn_did);
                    let start_facts: &CriticalPaths<BaseVar> = self.context_and_fn_to_fact_map
                        .get(&(fn_did, Context::User))
                        .unwrap().get(&START_STMT).unwrap();
                    let concerning_paths: Vec<_> = start_facts.iter().filter_map(|(path, _)| {
                        if path.of_argument() && mir_info.is_path_exported(path.as_ref()) {
                            let path_string = format!("{:?}", path);
                            Some(
                                mir_info.get_ast_name(path.base()).map(|name| {
                                    let ugly_name = format!("{:?}", path.base());
                                    // TODO: report criticalness
                                    let pretty_name = format!("{}", name);
                                    path_string.replace(&ugly_name, &pretty_name)
                                }).unwrap_or(path_string)
                            )
                        } else { None }
                    }).collect();
                    if concerning_paths.len() == 0 {
                        None
                    } else {
                        let fn_name = self.info.tcx.item_path_str(fn_did);
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
            }
            else {
                None
            }
        }).collect()
    }
}

pub fn paths_to_field<'a, 'mir, 'gcx: 'tcx, 'tcx: 'mir + 'a>(
    mir_info: MIRInfo<'a, 'mir, 'tcx, 'gcx>,
    field_did: DefId)
    -> Vec<Path<BaseVar>>
{
    let mut paths : Vec<Path<BaseVar>> = mir_info.args_and_tys().into_iter().flat_map(|(arg_id, ty)| {
        paths_to_field_acc(&mut Path::from_base(BaseVar::Arg(arg_id)), ty, field_did, mir_info.tcx())
    }).collect();
    paths.retain(|path| path.as_ref().has_indirection());
    paths.extend(paths_to_field_acc(&mut Path::from_base(BaseVar::ReturnPointer),
                                    mir_info.lvalue_ty(&Lvalue::ReturnPointer),
                                    field_did,
                                    mir_info.tcx()));
    paths
}

