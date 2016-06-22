// Alex Ozdemir <aozdemir@hmc.edu>
//
// A backwards data-flow analysis for determining when functions are dereferencing unverified types
// entered by a public interface.

use rustc::hir::{self, intravisit};
use rustc::mir::repr::{BasicBlock,
                       Constant,
                       Literal,
                       Lvalue,
                       Mir,
                       Operand,
                       Rvalue,
                       START_BLOCK,
                       StatementKind,
                       TerminatorKind,
};
use rustc::mir::traversal;
use rustc::mir::mir_map::MirMap;
use rustc::ty;
use rustc_data_structures::indexed_vec::Idx;

use base_var::{BaseVar,
               lvalue_to_var,
               lvalue_used_vars,
               operand_used_vars,
               rvalue_used_vars,
               lvalue_ptr_derefs,
               operand_ptr_derefs,
               rvalue_ptr_derefs,
};

use dep_graph::KeyedDepGraph;

use syntax::ast::NodeId;
use syntax::codemap::Span;

use std::collections::{BTreeSet,HashSet,HashMap,VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::{self,IntoIterator};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
// A unique index for each statement in a MIR. First, the basic block, then the position of the
// statment in the basic block. Often this is used to refer to positions between statements, in
// which case (_,0) is before the first statement in the BB, and (_,bb.len()) is after the last.
pub struct StatementIdx(BasicBlock,usize);

const START_STMT: StatementIdx = StatementIdx(START_BLOCK, 0);

pub type Context<Fact> = BTreeSet<Fact>;
pub type MIRFactsMap<Fact> = HashMap<StatementIdx,HashSet<Fact>>;
pub type CrateFactsMap<Fact> = HashMap<FullCx<Fact>,MIRFactsMap<Fact>>;

pub struct CrateInfo<'mir,'tcx:'mir> {
    // The MIRs for the crate
    pub mir_map: &'mir MirMap<'tcx>,

    // The Type Context, also includes the map from DefId's to NodeId's
    pub tcx: ty::TyCtxt<'mir,'tcx,'tcx>,
}

pub type FullCx<Fact> = (NodeId, Context<Fact>);

pub struct AnalysisState<'mir,'tcx:'mir,Fact> {
    // Holds the fact map for each MIR, in each context
    pub context_and_fn_to_fact_map: CrateFactsMap<Fact>,

    // The work queue, which also manages inter-function dependencies.
    pub queue: WorkQueue<Fact>,

    // Info about the crate, independent of the analysis
    pub info: CrateInfo<'mir,'tcx>,
}

/// The WorkQueue data structure not only provides a queue of analyses (MIR,CX) to run, it also
/// store inter-analysis depedencies, and enqeue analyses appropriatedly.
pub struct WorkQueue<Fact> {

    /// The data structure which stores all dependencies.
    deps: KeyedDepGraph<BasicBlock,FullCx<Fact>>,

    /// The queue of analyses to re-run.
    queue: VecDeque<FullCx<Fact>>,

    /// A map of where analyses in the queue need to be re-run from.
    map: HashMap<FullCx<Fact>,FlowSource>,

    /// A set of all things that have been enqueue. Relevant because the first time something is
    /// entered it's flow source should be all returns.
    entered: HashSet<FullCx<Fact>>,
}


impl<Fact: Hash + Eq + Clone> WorkQueue<Fact> {

    pub fn new<I: Iterator<Item=FullCx<Fact>>>(iter: I) -> WorkQueue<Fact> {
        let mut q = WorkQueue {
            deps: KeyedDepGraph::new(),
            queue: VecDeque::new(),
            map: HashMap::new(),
            entered: HashSet::new(),
        };
        iter.map(|full_cx| q.enqueue_many(full_cx, iter::once(START_BLOCK))).count();
        q
    }

    /// Register that `self_cx` depends on `dep_cx` from basic block `origin`.
    /// This records the dependency so that when the analysis of `dep_cx` changes in the future,
    /// `self_cx` will be resubmitted to the queue, to be re-analyzed from `origin`.
    /// It also removes [0 or 1] old dependency of `self_cx` originating at `origin`. This include
    /// removing that depedency from the graph, and removing that origin from the queue.
    pub fn register_dependency(&mut self,
                               self_cx: &FullCx<Fact>,
                               dep_cx: FullCx<Fact>,
                               origin: BasicBlock) {
        if !self.entered.contains(&dep_cx) {
            self.enqueue_many(dep_cx.clone(), iter::once(origin))
        }
        self.map.get_mut(self_cx).map(|flow_source| match flow_source {
            &mut FlowSource::Blocks(ref mut blocks) => { blocks.remove(&origin); }
            _ => (),
        });
        self.deps.remove(&origin, self_cx);
        self.deps.insert(origin, self_cx.clone(), dep_cx);
    }

    /// Enqueue all the full contexts (MIR,CX) which depend on this one. As a reminder, when those
    /// dependencies are popped from the queue they will only be analyzed from basic blocks where
    /// the dependent's dependency originates. The queue will also never have duplicate full
    /// contexts.
    pub fn enqueue_dependents(&mut self,
                              self_cx: &FullCx<Fact>) {
        for (dep, origins) in self.deps.get_dependents_with_keys(self_cx.clone()) {
            self.enqueue_many(dep, origins.into_iter())
        }
    }


    fn enqueue_many<O: Iterator<Item=BasicBlock>>(&mut self, full_cx: FullCx<Fact>, origins: O) {
        if !self.entered.contains(&full_cx) {
            self.map.insert(full_cx.clone(), FlowSource::Returns);
            self.queue.push_back(full_cx.clone());
            self.entered.insert(full_cx);
        }
        else {
            if self.map.contains_key(&full_cx) {
                match self.map.get_mut(&full_cx).unwrap() {
                    &mut FlowSource::Blocks(ref mut blocks) => {
                        origins.map(|bb| blocks.insert(bb.clone())).count();
                    },
                    // If the item is already there with returns, it'll get this origin implicitly
                    _ => (),
                };
            } else {
                let mut set = HashSet::new();
                origins.map(|bb| set.insert(bb.clone())).count();
                self.map.insert(full_cx.clone(), FlowSource::Blocks(set));
                self.queue.push_back(full_cx);
            }
        }
    }

    pub fn get(&mut self) -> Option<WorkItem<Fact>> {
        self.queue.pop_front().map( |full_cx| {
            let source = self.map.remove(&full_cx).unwrap();
            // TODO. Make sure that the dependency still exists!
            WorkItem(full_cx.0, full_cx.1, source)
        })
    }
}

/// Flow that needs to be continued in some MIR.
///
/// The NodeId indicate which MIR, the Context indicates which facts should hold at returns, and
/// the FlowSource indicates where the flow should begin within the MIR.
pub struct WorkItem<Fact>(NodeId, Context<Fact>, FlowSource);

/// Where flow should begin in an MIR.
///
/// Either from the returns, or from specific blocks
pub enum FlowSource {
    Returns,
    Blocks(HashSet<BasicBlock>),
}

impl<'mir,'tcx, Fact: Eq + Hash + Ord + Clone> AnalysisState<'mir,'tcx,Fact> {
    fn new(mir_map: &'mir MirMap<'tcx>, tcx: ty::TyCtxt<'mir,'tcx,'tcx>)
           -> AnalysisState<'mir,'tcx,Fact> {
        AnalysisState {
            context_and_fn_to_fact_map: HashMap::new(),
            info: CrateInfo::new(mir_map, tcx),
            queue: WorkQueue::new(mir_map.map.keys().map(|id| (*id, BTreeSet::new()))),
        }
    }
}

impl<'mir,'tcx> CrateInfo<'mir,'tcx> {
    fn new(mir_map: &'mir MirMap<'tcx>, tcx: ty::TyCtxt<'mir,'tcx,'tcx>)
           -> CrateInfo<'mir,'tcx> {
        CrateInfo {
            mir_map: mir_map,
            tcx: tcx,
        }
    }

    // If there is MIR for the value of this operand, this functions finds its ID (assuming the
    // operand is just constant).
    fn get_fn_node_id(&self, func_op: &Operand<'tcx>) -> Option<NodeId> {
        use rustc::mir::repr::{};
        match func_op {
            &Operand::Constant(Constant{ literal: Literal::Item { def_id, .. }, .. }) =>
                self.tcx.map.as_local_node_id(def_id).and_then(|node_id|
                    if self.mir_map.map.contains_key(&node_id) { Some(node_id) }
                    else { None }
                ),
            _ => None,
        }
    }

    fn node_id_to_mir(&self, node_id: &NodeId) -> Option<&'mir Mir<'tcx>> {
        self.mir_map.map.get(node_id)
    }
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

pub struct EscapeAnalysis;


pub enum Expr<'a, 'tcx: 'a> {
    Lvalue(&'a Lvalue<'tcx>),
    Rvalue(&'a Rvalue<'tcx>),
    Operand(&'a Operand<'tcx>)
}

impl EscapeAnalysis {
    // Maps an LValue to the BaseVar representing its location.
    fn location(lvalue: &Lvalue) -> BaseVar {
        lvalue_to_var(lvalue)
    }

    // The base variables which contribute to the value of this expression
    fn inputs(expr: Expr) -> Vec<BaseVar> {
        use self::Expr::*;
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
}

impl BackwardsAnalysis for EscapeAnalysis {
    type Fact = BaseVar;

    // The base variables which are made critical by this expression
    fn generate<'a, 'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                      tcx: ty::TyCtxt<'mir,'gcx,'tcx>,
                                      expr: Expr<'a, 'tcx>) -> Vec<BaseVar> {
        use self::Expr::*;
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

        let location = EscapeAnalysis::location(lval);
        pre_facts.remove(&location);

        if outs.contains(&location) {
            pre_facts.extend(EscapeAnalysis::inputs(Expr::Rvalue(rval)));
        }

        pre_facts.extend(EscapeAnalysis::generate(mir, tcx, Expr::Lvalue(lval)));
        pre_facts.extend(EscapeAnalysis::generate(mir, tcx, Expr::Rvalue(rval)));
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

        if let &Operand::Constant(Constant { literal: Literal::Item{ ref def_id, .. }, .. }) = fn_op {
            println!("FN Call: {:?}", crate_info.tcx.lookup_item_type(*def_id));
            println!("FN Call: {:?}", crate_info.tcx.item_path_str(*def_id));
            println!("FN Call: {:?}", crate_info.tcx.lookup_item_type(*def_id).ty.sty);
            println!("FN Call: {:?}", def_id.index);
        }
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

        let mir = crate_info.node_id_to_mir(&mir_id).unwrap();
        for arg_op in arg_ops {
            new_pre_facts.extend(Self::generate(mir, crate_info.tcx, Expr::Operand(arg_op)));
        }
        new_pre_facts.extend(Self::generate(mir, crate_info.tcx, Expr::Operand(fn_op)));
        new_pre_facts.extend(Self::generate(mir, crate_info.tcx, Expr::Lvalue(dest)));
        (fn_id.map(|id| (id, call_context.clone())), new_pre_facts)
    }
    fn return_facts(context: &Context<Self::Fact>) -> HashSet<Self::Fact> {
        context.iter().map(|fact| fact.clone()).collect()
    }
    fn all_contexts() -> Vec<Context<Self::Fact>> {
        vec![iter::empty().collect(), iter::once(BaseVar::ReturnPointer).collect()]
    }
}

pub trait BackwardsAnalysis {
    type Fact: PartialEq + Eq + Hash + Clone + Copy + Debug + PartialOrd + Ord;
    // The facts which are made by evaluating this expression. Comes up during some terminators.
    fn generate<'a, 'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                      tcx: ty::TyCtxt<'mir,'gcx,'tcx>,
                                      expr: Expr<'a, 'tcx>) -> Vec<Self::Fact>;
    // Produces the set of facts before the execution of a statement.
    fn transfer<'mir,'gcx,'tcx>(mir: &Mir<'tcx>,
                                tcx: ty::TyCtxt<'mir,'gcx,'tcx>,
                                post_facts: &HashSet<Self::Fact>,
                                statement: &StatementKind<'tcx>)
                                -> HashSet<Self::Fact>;
    // Produces the set of facts before the call of a function
    fn fn_call_transfer<'mir,'tcx>(mir_id: NodeId,
                                   crate_info: &CrateInfo<'mir,'tcx>,
                                   context_and_fn_to_fact_map: &CrateFactsMap<Self::Fact>,
                                   post_facts: &HashSet<Self::Fact>,
                                   fn_op: &Operand<'tcx>,
                                   arg_ops: &Vec<Operand<'tcx>>,
                                   dest: &Lvalue<'tcx>)
                                   -> (Option<FullCx<Self::Fact>>, HashSet<Self::Fact>);
    // Produces the set of facts before a forward split in the CFG.
    fn join(many: Vec<&HashSet<Self::Fact>>) -> HashSet<Self::Fact>;

    // The set of facts before a return given the context
    fn return_facts(context: &Context<Self::Fact>) -> HashSet<Self::Fact>;

    // The list of all contexts a function may be called in
    fn all_contexts() -> Vec<Context<Self::Fact>>;

    fn flow<'mir,'tcx>(mir_map: &'mir MirMap<'tcx>,
                       tcx: ty::TyCtxt<'mir,'tcx,'tcx>)
                       -> AnalysisState<'mir,'tcx,Self::Fact> {
        let mut state = AnalysisState::new(mir_map, tcx);
        while let Some(work_item) = state.queue.get() {
            Self::flow_work_item(work_item, &mut state);
        }
        state
    }

    /// Flows till convergence on a single (MIR,CX) - just looks up the results of other functions.
    /// Manipulates the state - changing (MIR,CX) dependencies and the queue.
    fn flow_work_item<'mir,'tcx>(
        work_item: WorkItem<Self::Fact>,
        state: &mut AnalysisState<Self::Fact>
    ) {

        // If the terminator just evaluates an expression (no assignment), this produces that
        // expression.
        fn evaluated_expression<'a, 'tcx: 'a>(
            kind: &'a TerminatorKind<'tcx>
        ) -> Option<Expr<'a, 'tcx>> {
            use rustc::mir::repr::TerminatorKind::*;
            match kind {
                &If { ref cond, .. } |
                &Assert { ref cond, .. } => Some(Expr::Operand(cond)),
                &Switch { discr: ref lval, .. } |
                &SwitchInt { discr: ref lval, .. } |
                &Drop { location: ref lval, .. } => Some(Expr::Lvalue(lval)),
                _ => None,
            }
        }
        let WorkItem(mir_id, context, flow_source) = work_item;
        let full_cx = (mir_id, context.clone());
        let mir = state.info.mir_map.map.get(&mir_id).unwrap();
        println!("Pulling full ctx {:?}", full_cx);
        let mut mir_facts = state.context_and_fn_to_fact_map.remove(&full_cx)
            .unwrap_or(HashMap::new());

        // Initialize work queue with Basic Blocks from the flow source
        let mut bb_queue: VecDeque<BasicBlock> = VecDeque::new();
        match flow_source {
            FlowSource::Returns => {
                println!("  BB Queue Initialized with all returns");
                for (bb_idx, bb_data) in traversal::postorder(&mir) {
                    use rustc::mir::repr::TerminatorKind::*;
                    //TODO: do Resume / Unreachable matter at all?
                    match bb_data.terminator().kind {
                        Return => bb_queue.push_back(bb_idx),
                        _ => (),
                    };
                }
            },
            FlowSource::Blocks(blocks) => bb_queue.extend(blocks),
        }
        println!("  Initial BB Queue: {:?}", bb_queue);

        // Save start facts for comparison, so we know whether to update dependencies
        let start_facts = mir_facts.get(&START_STMT).map(|facts| facts.clone());

        while let Some(bb_idx) = bb_queue.pop_front() {
            println!("  Visiting BB {:?}", bb_idx);
            let ref basic_block = mir[bb_idx];
            let mut new_flow = true;

            let pre_idx = StatementIdx(bb_idx, basic_block.statements.len());
            use rustc::mir::repr::TerminatorKind::*;
            match basic_block.terminator().kind {
                DropAndReplace{ ref location, ref value, ref target, .. } => {
                    let post_idx = StatementIdx(*target, 0);
                    let assignment = StatementKind::Assign(location.clone(),
                                                           Rvalue::Use(value.clone()));
                    if !Self::apply_transfer(&mir, state.info.tcx, &mut mir_facts,
                                            pre_idx, post_idx, &assignment) {
                        new_flow = false;
                    }
                },
                // TODO handle non-static calls
                Call { destination: Some((ref lval, next_bb)), ref func, ref args, .. } => {
                    let post_idx = StatementIdx(next_bb, 0);
                    let empty_set: HashSet<Self::Fact> = HashSet::new();
                    let (maybe_dependency, new_pre_facts) =
                        Self::fn_call_transfer(mir_id, &state.info,
                                               &state.context_and_fn_to_fact_map,
                                               mir_facts.get(&post_idx).unwrap_or(&empty_set),
                                               func, args, lval);
                    if let Some(dep) = maybe_dependency {
                        println!("    Dependency on {:?}, from {:?}", dep, bb_idx);
                        // We don't want to register dependencies on ourselves.
                        if dep != full_cx {
                            state.queue.register_dependency(&full_cx, dep, bb_idx);
                        }
                    }

                    let change = mir_facts.remove(&pre_idx).map(|pre_facts|
                        pre_facts != new_pre_facts
                    ).unwrap_or(true);
                    if !change { new_flow = false; }
                    mir_facts.insert(pre_idx, new_pre_facts);
                },
                Return => {
                    let new_pre_facts = Self::return_facts(&context);
                    let change = mir_facts.remove(&pre_idx).map(|pre_facts|
                        pre_facts != new_pre_facts
                    ).unwrap_or(true);
                    if !change { new_flow = false; }
                    mir_facts.insert(pre_idx, new_pre_facts);
                },
                ref other => {
                    let mut new_pre_facts = {
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
                    evaluated_expression(other).map(|expr|
                        new_pre_facts.extend(Self::generate(mir, state.info.tcx, expr))
                    );
                    let change = mir_facts.remove(&pre_idx).map(|pre_facts|
                        pre_facts != new_pre_facts
                    ).unwrap_or(true);
                    if !change { new_flow = false; }
                    mir_facts.insert(pre_idx, new_pre_facts);
                }
            }
            println!("    New Flow: {:?}", new_flow);
            if new_flow {
                for (s_idx, statement) in basic_block.statements.iter().enumerate().rev() {
                    let post_idx = StatementIdx(bb_idx, s_idx + 1);
                    let pre_idx = StatementIdx(bb_idx, s_idx);
                    if !Self::apply_transfer(&mir, state.info.tcx, &mut mir_facts,
                                             pre_idx, post_idx, &statement.kind) {
                        new_flow = false;
                        break;
                    }
                }
            }
            if new_flow {
                mir.predecessors_for(bb_idx).iter().map(|pred_idx|
                    bb_queue.push_back(*pred_idx)
                ).count();
            }
            println!("  BB Queue: {:?}", bb_queue);
        }

        if mir_facts.get(&START_STMT) != start_facts.as_ref() {
            // If our start facts changed, we've got to work on the dependencies
            state.queue.enqueue_dependents(&full_cx);
        }
        println!("Putting back ctx {:?}", full_cx);
        //print_map_lines(&mir_facts);
        state.context_and_fn_to_fact_map.insert(full_cx, mir_facts);
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


pub fn get_unsafe_fn_ids<'a>(hir: &'a hir::Crate) -> HashSet<NodeId> {
    let mut visitor = UnsafeIdLister{ set: HashSet::new() };
    hir.visit_all_items(&mut visitor);
    visitor.set
}

struct UnsafeIdLister {
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
