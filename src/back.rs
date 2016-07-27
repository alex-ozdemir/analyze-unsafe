// Alex Ozdemir <aozdemir@hmc.edu>
//
// A backwards data-flow analysis for determining when functions are dereferencing unverified types
// entered by a public interface.

use rustc::hir::{self, intravisit};
use rustc::hir::def_id::DefId;
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

use dep_graph::KeyedDepGraph;

use syntax::ast::NodeId;
use syntax::codemap::Span;

use std::collections::{BTreeSet,HashSet,HashMap,VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::{self,IntoIterator};

use std::io::Write;
macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);


#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
// A unique index for each statement in a MIR. First, the basic block, then the position of the
// statment in the basic block. Often this is used to refer to positions between statements, in
// which case (_,0) is before the first statement in the BB, and (_,bb.len()) is after the last.
pub struct StatementIdx(BasicBlock,usize);

pub const START_STMT: StatementIdx = StatementIdx(START_BLOCK, 0);

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

    /// If this function is static, gets the def'n ID.
    /// Otherwise returns none.
    pub fn get_fn_def_id(&self, func_op: &Operand<'tcx>) -> Option<DefId> {
        match func_op {
            &Operand::Constant(Constant{ literal: Literal::Item { def_id, .. }, .. }) =>
                Some(def_id),
            _ => None,
        }
    }

    // If there is MIR for the value of this operand, this functions finds its ID (assuming the
    // operand is just constant).
    pub fn get_fn_node_id(&self, func_op: &Operand<'tcx>) -> Option<NodeId> {
        self.get_fn_def_id(func_op).and_then(|def_id| self.tcx.map.as_local_node_id(def_id)
            .and_then(|node_id|
                if self.mir_map.map.contains_key(&node_id) { Some(node_id) }
                else { None }
                ))
    }

    pub fn node_id_to_mir(&self, node_id: &NodeId) -> Option<&'mir Mir<'tcx>> {
        self.mir_map.map.get(node_id)
    }
}

pub enum Expr<'a, 'tcx: 'a> {
    Lvalue(&'a Lvalue<'tcx>),
    Rvalue(&'a Rvalue<'tcx>),
    Operand(&'a Operand<'tcx>)
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
        errln!("Pulling full ctx {:?}", full_cx);
        let mut mir_facts = state.context_and_fn_to_fact_map.remove(&full_cx)
            .unwrap_or(HashMap::new());

        // Initialize work queue with Basic Blocks from the flow source
        let mut bb_queue: VecDeque<BasicBlock> = VecDeque::new();
        match flow_source {
            FlowSource::Returns => {
                errln!("  BB Queue Initialized with all returns");
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
        errln!("  Initial BB Queue: {:?}", bb_queue);

        // Save start facts for comparison, so we know whether to update dependencies
        let start_facts = mir_facts.get(&START_STMT).map(|facts| facts.clone());

        while let Some(bb_idx) = bb_queue.pop_front() {
            errln!("  Visiting BB {:?}", bb_idx);
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
                        errln!("    Dependency on {:?}, from {:?}", dep, bb_idx);
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
                    let new_pre_facts = context.iter().cloned().collect();
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
            errln!("    New Flow: {:?}", new_flow);
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
            errln!("  BB Queue: {:?}", bb_queue);
        }

        if mir_facts.get(&START_STMT) != start_facts.as_ref() {
            // If our start facts changed, we've got to work on the dependencies
            state.queue.enqueue_dependents(&full_cx);
        }
        errln!("Putting back ctx {:?}", full_cx);
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
            //errln!("Meaningful transfer from {:?} -> {:?}:", pre_idx, post_idx);
            //errln!("  Statement: {:?}", statement);
            //errln!("  Old (Pre): {:?}", old_facts);
            //errln!("  New (Pre): {:?}", new_pre_facts);
            //errln!("  Post     : {:?}", mir_facts.get(&post_idx).unwrap());
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
    errln!("Map:");
    for (key, val) in map.iter() {
        errln!("  {:?} : {:?}", key, val);
    }
}
