
use rustc::hir::{self, intravisit};
use rustc::mir::repr::{self,BasicBlock,Lvalue,Mir,Operand,Rvalue,START_BLOCK,StatementKind};
use rustc::mir::traversal;
use rustc::mir::mir_map::MirMap;
use rustc::ty;
use rustc_data_structures::indexed_vec::Idx;

use dataflow::{BaseVar,lvalue_to_var,operand_used_vars,rvalue_ptr_derefs,rvalue_used_vars};

use syntax::ast::NodeId;
use syntax::codemap::Span;

use std::collections::{HashSet,HashMap};
use std::hash::Hash;
use std::fmt::Debug;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
// A unique index for each statement in a MIR. First, the basic block, then the position of the
// statment in the basic block. Often this is used to refer to positions between statements, in
// which case (_,0) is before the first statement in the BB, and (_,bb.len()) is after the last.
pub struct StatementIdx(BasicBlock,usize);

const START_STMT: StatementIdx = StatementIdx(START_BLOCK, 0);

pub type MIRFactsMap<Fact> = HashMap<StatementIdx,HashSet<Fact>>;
pub type CrateFactsMap<Fact> = HashMap<NodeId,MIRFactsMap<Fact>>;

pub struct AnalysisState<'mir,'tcx: 'mir,Fact> {
    // Holds the fact map for each MIR, as called with a non-critical return
    pub crate_fact_maps_normal_return: CrateFactsMap<Fact>,

    // Holds the fact map for each MIR, as called with a critical return
    pub crate_fact_maps_critical_return: CrateFactsMap<Fact>,

    // The MIRs for the crate
    pub mir_map: &'mir MirMap<'tcx>,

    // The Type Context, also includes the map from DefId's to NodeId's
    pub tcx: ty::TyCtxt<'mir,'tcx,'tcx>,
}

impl<'mir,'tcx, Fact> AnalysisState<'mir,'tcx,Fact> {
    fn new(mir_map: &'mir MirMap<'tcx>, tcx: ty::TyCtxt<'mir,'tcx,'tcx>)
           -> AnalysisState<'mir,'tcx,Fact> {
        AnalysisState{
            mir_map: mir_map,
            tcx: tcx,
            crate_fact_maps_normal_return: HashMap::new(),
            crate_fact_maps_critical_return: HashMap::new()
        }
    }

    // If there is MIR for the value of this operand, this functions finds it (assuming the operand
    // is just constant).
    fn get_fn_node_id(&self, func_op: &Operand<'tcx>) -> Option<NodeId> {
        match func_op {
            &repr::Operand::Constant(repr::Constant{ literal: repr::Literal::Item { def_id, .. }, .. }) =>
                self.tcx.map.as_local_node_id(def_id).and_then(|node_id|
                    if self.mir_map.map.contains_key(&node_id) { Some(node_id) }
                    else { None }
                ),
            _ => None,
        }
    }

    fn get_crate_facts_map(&mut self, return_is_critical: bool) -> &mut CrateFactsMap<Fact> {
        if return_is_critical {
            &mut self.crate_fact_maps_critical_return
        } else {
            &mut self.crate_fact_maps_normal_return
        }
    }

    fn node_id_to_mir(&self, node_id: &NodeId) -> Option<&'mir Mir<'tcx>> {
        self.mir_map.map.get(node_id)
    }
}

impl<'mir,'tcx> AnalysisState<'mir,'tcx,BaseVar> {
    pub fn get_concerns(&self,
                        analysis: &ty::CrateAnalysis,
                        hir: &hir::Crate)
                        -> Vec<(Span,String)> {
        let unsafe_fn_ids = get_unsafe_fn_ids(hir);
        analysis.access_levels.map.iter().filter(|&(id, _)|
            !unsafe_fn_ids.contains(id)
        ).filter_map(|(id, _)| {
            self.node_id_to_mir(id).and_then(|mir| {
                //println!("The function with id {:?} has access level {:?}", id, access_level);
                let start_facts = self.crate_fact_maps_normal_return.get(id).unwrap()
                    .get(&START_STMT).unwrap();
                let concerning_arguments: Vec<_> = start_facts.iter().filter_map(|var| {
                    match var {
                        &BaseVar::Arg(arg_idx) => Some(mir.arg_decls[arg_idx].debug_name),
                        _ => None,
                    }
                }).collect();
                if concerning_arguments.len() == 0 {
                    None
                } else {
                    let fn_name = self.tcx.item_path_str(self.tcx.map.local_def_id(*id));
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

pub struct EscapeAnalysis;
impl BackwardsAnalysis for EscapeAnalysis {
    type Fact = BaseVar;
    fn transfer<'mir,'gcx,'tcx>(mir: &Mir<'tcx>,
                           tcx: ty::TyCtxt<'mir,'gcx,'tcx>,
                           outs: &HashSet<Self::Fact>,
                           statement: &StatementKind<'tcx>)
                           -> HashSet<Self::Fact> {
        let mut pre_facts = HashSet::new();
        let &StatementKind::Assign(ref lval, ref rval) = statement;
        let lval_fact = lvalue_to_var(lval);
        outs.iter().map(|fact| pre_facts.insert(*fact)).count();
        pre_facts.remove(&lval_fact);
        if outs.contains(&lval_fact) {
            let mut used_vars = vec![];
            rvalue_used_vars(rval, &mut used_vars);
            used_vars.into_iter().map(|fact| pre_facts.insert(fact)).count();
        }
        let mut vars_used_for_derefs = vec![];
        rvalue_ptr_derefs(mir, tcx, rval, &mut vars_used_for_derefs);
        //if vars_used_for_derefs.len() > 0 {
            //println!("`{:?}` derefs {:?}", statement, vars_used_for_derefs);
        //}
        vars_used_for_derefs.into_iter().map(|fact| pre_facts.insert(fact)).count();
        pre_facts
    }
    fn join(many: Vec<&HashSet<Self::Fact>>) -> HashSet<Self::Fact> {
        let mut pre_facts = HashSet::new();
        many.iter().map(|facts| facts.iter().map(|fact| pre_facts.insert(*fact)).count()).count();
        pre_facts
    }
    fn lvalue_to_fact(lvalue: &Lvalue) -> Self::Fact {
        lvalue_to_var(lvalue)
    }
    fn operand_to_facts(op: &Operand) -> Vec<BaseVar> {
        let mut out = vec![];
        operand_used_vars(op, &mut out);
        out
    }
    fn return_facts() -> Vec<Self::Fact> {
        vec![BaseVar::ReturnPointer]
    }
    fn fact_to_input_idx(fact: Self::Fact) -> Option<usize> {
        match fact {
            BaseVar::Arg(arg) => Some(arg.index()),
            _ => None,
        }
    }
}

pub trait BackwardsAnalysis {
    type Fact: PartialEq + Eq + Hash + Clone + Copy + Debug;
    fn transfer<'mir,'gcx,'tcx>(mir: &Mir<'tcx>,
                                tcx: ty::TyCtxt<'mir,'gcx,'tcx>,
                                outs: &HashSet<Self::Fact>,
                                statement: &StatementKind<'tcx>)
                                -> HashSet<Self::Fact>;
    fn join(many: Vec<&HashSet<Self::Fact>>) -> HashSet<Self::Fact>;
    fn lvalue_to_fact(lvalue: &Lvalue) -> Self::Fact;
    fn operand_to_facts(op: &Operand) -> Vec<Self::Fact>;
    fn return_facts() -> Vec<Self::Fact>;
    fn fact_to_input_idx(fact: Self::Fact) -> Option<usize>;
    fn flow<'mir,'tcx>(mir_map: &'mir MirMap<'tcx>,
                       tcx: ty::TyCtxt<'mir,'tcx,'tcx>)
                       -> AnalysisState<'mir,'tcx,Self::Fact> {
        let mut state = AnalysisState::new(mir_map, tcx);
        let mut stable = false;
        while !stable {
            stable = true;
            for (mir_id, _) in state.mir_map.map.iter() {
                if Self::flow_mir(*mir_id, &mut state, false) {stable = false;}
                if Self::flow_mir(*mir_id, &mut state, true) {stable = false;}
            }
        }
        state
    }

    // Flows till convergence
    fn flow_mir<'mir,'tcx>(mir_id: NodeId,
                           state: &mut AnalysisState<Self::Fact>,
                           return_is_critical: bool)
                           -> bool {
        let mir = state.mir_map.map.get(&mir_id).unwrap();
        let mut mir_facts = state.get_crate_facts_map(return_is_critical)
                                 .remove(&mir_id).unwrap_or(HashMap::new());

        let mut any_change = false;
        let mut stable = false;
        while !stable {
            //println!("Starting {:?}, critical: {}", mir_id, return_is_critical);
            stable = true;
            for (bb_idx, basic_block) in traversal::postorder(&mir) {
                //println!("BB {:?}", bb_idx);
                let pre_idx = StatementIdx(bb_idx, basic_block.statements.len());
                use rustc::mir::repr::TerminatorKind::*;
                match basic_block.terminator().kind {
                    DropAndReplace{ ref location, ref value, ref target, .. } => {
                        let post_idx = StatementIdx(*target, 0);
                        let assignment = StatementKind::Assign(location.clone(), Rvalue::Use(value.clone()));
                        if Self::apply_transfer(mir, state.tcx, &mut mir_facts, pre_idx, post_idx, &assignment) {
                            stable = false;
                        }
                    },
                    Call { destination: Some((ref lval, next_bb)), ref func, ref args, .. } => {
                        let fn_id = state.get_fn_node_id(func);
                        let post_idx = StatementIdx(next_bb, 0);
                        let result_is_critical = mir_facts.get(&post_idx).unwrap().contains(&Self::lvalue_to_fact(lval));
                        let arg_indices = fn_id.map_or_else(|| {
                            (0..args.len()).collect::<Vec<_>>()
                        }, |id| {
                            let mut func_map = if result_is_critical {
                                &mut state.crate_fact_maps_critical_return
                            } else {
                                &mut state.crate_fact_maps_critical_return
                            };
                            let relevant_facts = func_map.entry(id).or_insert(HashMap::new()).entry(START_STMT).or_insert(HashSet::new());
                            let mut indices = relevant_facts.iter().filter_map(
                                |fact| Self::fact_to_input_idx(*fact)
                            ).collect::<Vec<_>>();
                            indices.sort();
                            indices
                        });
                        let pre_facts = mir_facts.remove(&pre_idx).unwrap_or(HashSet::new());
                        let mut new_pre_facts = Self::join(vec![mir_facts.get(&post_idx).unwrap()]);
                        new_pre_facts.remove(&Self::lvalue_to_fact(lval));
                        if result_is_critical || fn_id.is_some() {
                            for arg_idx in arg_indices.iter() {
                                let arg_facts = Self::operand_to_facts(&args[*arg_idx]);
                                for fact in arg_facts {
                                    new_pre_facts.insert(fact);
                                }
                            }
                        }
                        if pre_facts != new_pre_facts { stable = false; }
                        mir_facts.insert(pre_idx, new_pre_facts);
                    },
                    Return => {
                        let pre_facts = mir_facts.entry(pre_idx).or_insert(HashSet::new());
                        if return_is_critical {
                            for fact in Self::return_facts() {
                                if !pre_facts.contains(&fact) {
                                    stable = false;
                                    pre_facts.insert(fact);
                                }
                            }
                        }
                    },
                    ref other => {
                        let new_pre_facts = {
                            let mut post_facts = vec![];
                            for succ_bb_idx in other.successors().iter() {
                                let post_idx = StatementIdx(*succ_bb_idx, 0);
                                if !mir_facts.contains_key(&post_idx) {
                                    mir_facts.insert(post_idx, HashSet::new());
                                }
                            }
                            for succ_bb_idx in other.successors().iter() {
                                let post_idx = StatementIdx(*succ_bb_idx, 0);
                                post_facts.push(mir_facts.get(&post_idx).unwrap());
                            }
                            Self::join(post_facts)
                        };
                        let change = new_pre_facts != *mir_facts.entry(pre_idx).or_insert(HashSet::new());
                        if change {
                            stable = false;
                            mir_facts.insert(pre_idx, new_pre_facts);
                        }
                    }
                }
                for (s_idx, statement) in basic_block.statements.iter().enumerate().rev() {
                    let post_idx = StatementIdx(bb_idx, s_idx + 1);
                    let pre_idx = StatementIdx(bb_idx, s_idx);
                    if Self::apply_transfer(mir, state.tcx, &mut mir_facts, pre_idx, post_idx, &statement.kind) {
                        stable = false;
                    }
                }
            }
            if !stable {
                any_change = true;
            }
            //print!("Escape: {:?} (critical {}):", mir_id, return_is_critical);
            //print_map_lines(&mir_facts);
        }
        state.get_crate_facts_map(return_is_critical).insert(mir_id, mir_facts);
        any_change
    }


    /// Apply the transfer function across this statment, which must lie between the two indices.
    /// Returns whether or not the facts for `pre_idx` actually changed because of the transfer
    /// function, so that the caller can detect when the flow stabilizes.
    fn apply_transfer<'mir,'gcx,'tcx>(mir: &Mir<'tcx>,
                                      tcx: ty::TyCtxt<'mir,'gcx,'tcx>,
                                      mir_facts: &mut MIRFactsMap<Self::Fact>,
                                      pre_idx: StatementIdx,
                                      post_idx: StatementIdx,
                                      statement: &StatementKind<'tcx>)
                                      -> bool {
        let new_pre_facts = {
            let post_facts = mir_facts.entry(post_idx).or_insert(HashSet::new());
            Self::transfer(mir, tcx, post_facts, statement)
        };
        let old_facts = mir_facts.remove(&pre_idx);
        let change = old_facts.as_ref().map_or(true, |facts| *facts != new_pre_facts);
        //if change {
            //println!("Meaningful transfer from {:?} -> {:?}:", pre_idx, post_idx);
            //println!("  Statement: {:?}", statement);
            //println!("  Old (Pre): {:?}", old_facts);
            //println!("  New (Pre): {:?}", new_pre_facts);
            //println!("  Post     : {:?}", mir_facts.get(&post_idx).unwrap());
        //}
        mir_facts.insert(pre_idx, new_pre_facts);
        change
    }

}

fn get_unsafe_fn_ids<'a>(hir: &'a hir::Crate) -> HashSet<NodeId> {
    let mut visitor = UnsafeIdLister{ set: HashSet::new() };
    hir.visit_all_items(&mut visitor);
    visitor.set
}

pub struct UnsafeIdLister {
    pub set: HashSet<NodeId>
}

impl<'v> intravisit::Visitor<'v> for UnsafeIdLister {
    fn visit_fn(&mut self, fn_kind: intravisit::FnKind<'v>, _: &'v hir::FnDecl,
                _: &'v hir::Block, _: Span, id: NodeId) {
        use rustc::hir::intravisit::FnKind::*;
        match fn_kind {
            ItemFn(_, _, hir::Unsafety::Unsafe, _, _, _, _) |
            Method(_, &hir::MethodSig{unsafety: hir::Unsafety::Unsafe, ..} , _, _) =>
                {self.set.insert(id);},
            _ => (),
        };
    }
}


#[allow(dead_code)]
fn print_map_lines<K: Debug + Eq + Hash, V: Debug>(map: &HashMap<K, V>) {
    println!("Map:");
    for (key, val) in map.iter() {
        println!("  {:?} : {:?}", key, val);
    }
}
