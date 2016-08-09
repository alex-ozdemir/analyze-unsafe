// Alex Ozdemir <aozdemir@hmc.edu>
//
// A backwards data-flow analysis for determining when functions are dereferencing unverified types
// entered by a public interface.
//
// This flow tool is for the complex data flow.

use rustc::hir::{self, intravisit};
use rustc::traits;
use syntax_pos::{BytePos, NO_EXPANSION};
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
                       Var,
                       Arg,
};

use base_var::BaseVar;

use rustc_data_structures::indexed_vec::Idx;

use rustc::mir::traversal;
use rustc::mir::mir_map::MirMap;
use rustc::middle::privacy::AccessLevels;
use rustc::ty::{self,TyCtxt,TypeVariants,Ty};

use dep_graph::KeyedDepGraph;

use syntax::ast::{self,NodeId};
use syntax::codemap::Span;

use std::collections::{BTreeMap,HashSet,HashMap,VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::{self,IntoIterator};

use path::{Path,PathRef};

use std::io::Write;
macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
// A unique index for each statement in a MIR. First, the basic block, then the position of the
// statment in the basic block. Often this is used to refer to positions between statements, in
// which case (_,0) is before the first statement in the BB, and (_,bb.len()) is after the last.
pub struct StatementIdx(BasicBlock,usize);

pub const START_STMT: StatementIdx = StatementIdx(START_BLOCK, 0);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Context<Facts> {
    /// This indicates the context which could exist when the function is called by the user. It is
    /// influence by the private fields which have been made critical.
    User,
    Internal(Facts),
}
pub type RawContext<Facts> = Facts;
pub type MIRFactsMap<Facts> = BTreeMap<StatementIdx,Facts>;
pub type CrateFactsMap<Facts> = BTreeMap<AnalysisUnit<Facts>,MIRFactsMap<Facts>>;

#[derive(Clone, Copy)]
pub struct MIRInfo<'a, 'mir, 'gcx: 'tcx, 'tcx: 'mir + 'a>{
    mir: &'a Mir<'tcx>,
    tcx: TyCtxt<'mir, 'gcx, 'tcx>,
    access_levels: &'a AccessLevels,
    /// This flag indicates whether MIRInfo should skip the sound alias analysis in favor of an
    /// optimistic one (all distinct paths not may alias).
    ///
    /// This is used when assigning actual parameters to formal ones, and is a pretty dirty Hack.
    /// The right way to do it is to abstract out the functionality of MIRInfo as traits such as
    /// 'AliasKnoweldge' and 'TypeKnowledge', and then program generically.
    ///
    /// This would allow us to swap in a new alias logic as needed.
    ///
    /// But for now ...
    optimistic_alias: bool,
}

impl<'a, 'mir, 'gcx, 'tcx> MIRInfo<'a, 'mir, 'gcx, 'tcx> {
    pub fn lvalue_ty(&self, lvalue: &Lvalue<'tcx>) -> Ty<'tcx> {
        &self.mir.lvalue_ty(self.tcx, lvalue).to_ty(self.tcx)
    }

    pub fn is_raw_ptr(&self, lvalue: &Lvalue<'tcx>) -> bool {
        if let TypeVariants::TyRawPtr(_) = self.lvalue_ty(lvalue).sty {
            true
        } else { false }
    }

    pub fn is_ref(&self, lvalue: &Lvalue<'tcx>) -> bool {
        if let TypeVariants::TyRef(_,_) = self.lvalue_ty(lvalue).sty {
            true
        } else { false }
    }

    pub fn set_optimistic_alias(&mut self, optimistic: bool) {
        self.optimistic_alias = optimistic;
    }

    #[allow(unused_variables)]
    pub fn singular(&self, p1: PathRef<BaseVar>) -> bool { false }

    pub fn must_alias<'b>(&self, p1: PathRef<'b, BaseVar>, p2: PathRef<'b, BaseVar>) -> bool {
        p1 == p2
    }

    pub fn may_alias<'b>(&self, p1: PathRef<'b, BaseVar>, p2: PathRef<'b, BaseVar>) -> bool {
        if !self.optimistic_alias {
            p1 == p2
            || (
                (p1.has_indirection() || p2.has_indirection())
                && self.path_ty(p1) == self.path_ty(p2)
            )
        } else {
            p1 == p2
        }
    }

    // TODO: Fix this!
    pub fn may_reach<'b>(&self, p1: PathRef<'b, BaseVar>, p2: PathRef<'b, BaseVar>) -> bool {
        for (p2sub, _) in p2.sub_paths() {
            if self.may_alias(p1.clone(), p2sub) {
                return true;
            }
        }
        return false;
    }

    pub fn path_ty(&self, p1: PathRef<BaseVar>) -> Ty<'tcx> {
        use path::Projection::*;
        use rustc::ty::TypeVariants::*;
        let mut ty = Self::narrow_to_single_ty(self.base_var_ty(p1.base));
        for projection in p1.projections {
            match projection {
                &Deref => {
                    ty = ty.builtin_deref(true, ty::LvaluePreference::NoPreference)
                           .unwrap_or_else(|| {
                                bug!("Path {:?} deref'd the type {:?}", p1, ty)
                            }).ty
                }
                &Field(ref variant_idx, None) => {
                    match ty.sty {
                        TyEnum(_, _) => (),
                        _ => { bug!("Path {:?} _just_ downcasts the type {:?}, with variant {}",
                                    p1,
                                    ty,
                                    variant_idx); },
                    }
                }
                &Field(variant_idx, Some(field_idx)) => {
                    ty = match ty.sty {
                        TyTuple(ref inner_tys) if variant_idx == 0 => inner_tys[field_idx],
                        TyStruct(ref adt_def, ref substs) |
                        TyEnum(ref adt_def, ref substs) =>
                            adt_def.variants[variant_idx].fields[field_idx].ty(self.tcx, substs),
                        TyClosure(_, ref closure_substs) =>
                            closure_substs.upvar_tys[field_idx],
                        _ => bug!("Path {:?} specifies field ({},{}) of type {:?}",
                                  p1,
                                  variant_idx,
                                  field_idx,
                                  ty),
                    }
                }
            }
            ty = Self::narrow_to_single_ty(ty);
        }
        //errln!("      Path {:?} has type {:?}", p1, ty);
        ty
    }

    /// Returns true if the indicated PathRef corresponds to a publically visible location.
    /// Public fields of exported structures count, as do primitive types, but nothing else does.
    pub fn is_path_exported(&self, p1: PathRef<BaseVar>) -> bool {
        use path::Projection::*;
        use rustc::ty::TypeVariants::*;
        let mut ty = Self::narrow_to_single_ty(self.base_var_ty(p1.base));
        for projection in p1.projections {
            match projection {
                &Deref => {
                    ty = ty.builtin_deref(true, ty::LvaluePreference::NoPreference)
                           .unwrap_or_else(|| {
                                bug!("Path {:?} deref'd the type {:?}", p1, ty)
                            }).ty
                }
                &Field(variant_idx, None) => {
                    let not_exported = match ty.sty {
                        TyEnum(ref adt_def, _) => {
                            let ref variant = adt_def.variants[variant_idx];
                            self.tcx.map.as_local_node_id(variant.did)
                            .map(|node_id| !self.access_levels.is_reachable(node_id))
                            .unwrap_or(false)
                        },
                        _ => { bug!("Path {:?} _just_ downcasts the type {:?}, with variant {}",
                                    p1,
                                    ty,
                                    variant_idx); },
                    };
                    if not_exported { bug!("Variant is not exported!") }
                },
                &Field(variant_idx, Some(field_idx)) => {
                    ty = match ty.sty {
                        TyTuple(ref inner_tys) if variant_idx == 0 => inner_tys[field_idx],
                        TyStruct(ref adt_def, ref substs) |
                        TyEnum(ref adt_def, ref substs) => {
                            let ref variant = adt_def.variants[variant_idx];
                            let not_exported = self.tcx.map.as_local_node_id(variant.did)
                                .map(|node_id| !self.access_levels.is_reachable(node_id))
                                .unwrap_or(false);
                            if not_exported {
                                bug!("Variant is not exported! {:?}, ty {:?}, var {:?}",
                                     p1, ty, variant.did);
                            }
                            let ref field = adt_def.variants[variant_idx].fields[field_idx];
                            if field.vis != ty::Visibility::Public {
                                return false;
                            }
                            field.ty(self.tcx, substs)
                        },
                        _ => bug!("Path {:?} specifies field ({},{}) of type {:?}",
                                  p1,
                                  variant_idx,
                                  field_idx,
                                  ty),
                    }
                }
            }
        }
        return true;
    }

    /// If this path has a private field in it, takes the extension from the private field to make
    /// a new path.
    pub fn path_from_private(&self, p1: PathRef<BaseVar>) -> Option<Path<DefId>> {
        use path::Projection::*;
        use rustc::ty::TypeVariants::*;
        let mut ty = Self::narrow_to_single_ty(self.base_var_ty(p1.base));
        for projection_idx in 0..(p1.projections.len()) {
            let ref projection = p1.projections[projection_idx];
            match projection {
                &Deref => {
                    ty = ty.builtin_deref(true, ty::LvaluePreference::NoPreference)
                           .unwrap_or_else(|| {
                                bug!("Path {:?} deref'd the type {:?}", p1, ty)
                            }).ty
                },
                &Field(variant_idx, None) => {
                    let not_exported = match ty.sty {
                        TyEnum(ref adt_def, _) => {
                            let ref variant = adt_def.variants[variant_idx];
                            self.tcx.map.as_local_node_id(variant.did)
                            .map(|node_id| !self.access_levels.is_reachable(node_id))
                            .unwrap_or(false)
                        },
                        _ => { bug!("Path {:?} _just_ downcasts the type {:?}, with variant {}",
                                    p1,
                                    ty,
                                    variant_idx); },
                    };
                    if not_exported { bug!("Variant is not exported!") }
                },
                &Field(variant_idx, Some(field_idx)) => {
                    ty = match ty.sty {
                        TyTuple(ref inner_tys) if variant_idx == 0 => inner_tys[field_idx],
                        TyStruct(ref adt_def, ref substs) |
                        TyEnum(ref adt_def, ref substs) => {
                            let ref variant = adt_def.variants[variant_idx];
                            let not_exported = self.tcx.map.as_local_node_id(variant.did)
                                .map(|node_id| !self.access_levels.is_reachable(node_id))
                                .unwrap_or(false);
                            if not_exported {
                                bug!("Variant is not exported! {:?}, ty {:?}, var {:?}",
                                     p1, ty, variant.did);
                            }
                            let ref field = variant.fields[field_idx];
                            if field.vis != ty::Visibility::Public {
                                let mut field_path = Path::from_base(field.did);
                                let extension = p1.projections.split_at(projection_idx+1).1;
                                field_path.extend_in_place(extension);
                                return Some(field_path);
                            }
                            field.ty(self.tcx, substs)
                        },
                        _ => bug!("Path {:?} specifies field ({},{}) of type {:?}",
                                  p1,
                                  variant_idx,
                                  field_idx,
                                  ty),
                    }
                }
            }
        }
        return None;
    }

    /// This function reduces array and slice types (collection types) to their component type. The
    /// reason we do this is the analysis does not record slice / index projections in the paths.
    /// Thus, when considering a path `*p` on a `p` with type [*const T], we need to skip over the
    /// [] and deref the *const T to get T.
    fn narrow_to_single_ty(mut ty: Ty<'tcx>) -> Ty<'tcx> {
        while let Some(inner_ty) = ty.builtin_index() {
            ty = inner_ty;
        }
        ty
    }

    fn base_var_ty(&self, base: &BaseVar) -> Ty<'tcx> {
        use base_var::BaseVar::*;
        match base {
            &Var(var) => self.lvalue_ty(&Lvalue::Var(var)),
            &Temp(temp) => self.lvalue_ty(&Lvalue::Temp(temp)),
            &Arg(arg) => self.lvalue_ty(&Lvalue::Arg(arg)),
            &Static(def_id) => self.lvalue_ty(&Lvalue::Static(def_id)),
            &ReturnPointer => self.lvalue_ty(&Lvalue::ReturnPointer),
        }
    }

    pub fn fresh_var(&self) -> Var {
        Var::new(self.mir.var_decls.len())
    }

    pub fn args_and_tys(&self) -> Vec<(Arg,Ty<'tcx>)> {
        self.mir.arg_decls.iter_enumerated()
            .map(|(arg_id, arg_decl)| (arg_id, arg_decl.ty))
            .collect()
    }

    pub fn tcx(&self) -> TyCtxt<'mir, 'tcx, 'gcx> {
        self.tcx
    }

    pub fn get_ast_name(&self, b: &BaseVar) -> Option<ast::Name> {
        match *b {
            BaseVar::Var(ref var) => Some(self.mir.var_decls[*var].name),
            BaseVar::Temp(_) => None,
            BaseVar::Arg(ref arg) => Some(self.mir.arg_decls[*arg].debug_name),
            BaseVar::Static(_) => None,
            BaseVar::ReturnPointer => None,
        }
    }
}

///// An option representing code that could be run at a dynamic dispatch site.
//#[derive(PartialEq,Eq,Hash,Debug,Clone,Copy)]
//pub enum DDOption {
//    /// Code (A mir_id) that we have (an can analyze).
//    Known(NodeId),
//    /// Unknown code - something we can't analyze.
//    Unknown,
//}

pub struct CrateInfo<'mir,'tcx:'mir> {
    // The MIRs for the crate
    pub mir_map: &'mir MirMap<'tcx>,

    // The privacy status of items
    pub access_levels: AccessLevels,

    // The Type Context, also includes the map from DefId's to NodeId's
    pub tcx: ty::TyCtxt<'mir,'tcx,'tcx>,
}

impl<'mir, 'tcx> CrateInfo<'mir, 'tcx> {
    pub fn get_mir_info<'a>(&'a self, mir_id: &NodeId) -> MIRInfo<'a, 'mir, 'tcx, 'tcx> {
        let mir = self.get_mir(mir_id);
        let ref access_levels = self.access_levels;
        MIRInfo {
            mir: mir,
            tcx: self.tcx.clone(),
            optimistic_alias: false,
            access_levels: access_levels,
        }
    }
    pub fn get_mir(&self, mir_id: &NodeId) -> &Mir<'tcx> {
        self.mir_map.map.get(mir_id).expect("CrateInfo created for an invalid MIRID")
    }
}

pub type AnalysisUnit<Facts> = (NodeId, Context<Facts>);
pub type RawAnalysisUnit<Facts> = (NodeId, RawContext<Facts>);

pub struct AnalysisState<'mir,'tcx:'mir,Facts,GlobalFacts> {
    // Holds the fact map for each MIR, in each context
    pub context_and_fn_to_fact_map: CrateFactsMap<Facts>,

    // The work queue, which also manages inter-function dependencies.
    pub queue: WorkQueue<Facts>,

    // Info about the crate, independent of the analysis
    pub info: CrateInfo<'mir,'tcx>,

    // Info about which private fields are currently critical
    // While the range is technically Facts, the base_variable actually doesn't matter.
    pub user_cx: GlobalFacts,
}

/// The WorkQueue data structure not only provides a queue of analyses (MIR,CX) to run, it also
/// store inter-analysis depedencies, and enqeue analyses appropriatedly.
pub struct WorkQueue<Facts> {

    /// The data structure which stores all dependencies.
    deps: KeyedDepGraph<BasicBlock,AnalysisUnit<Facts>>,

    /// The queue of analyses to re-run.
    queue: VecDeque<AnalysisUnit<Facts>>,

    /// A map of where analyses in the queue need to be re-run from.
    map: HashMap<AnalysisUnit<Facts>,FlowSource>,

    /// A set of all things that have been enqueue. Relevant because the first time something is
    /// entered it's flow source should be all returns.
    entered: HashSet<AnalysisUnit<Facts>>,

    /// A list of the functions in the crate
    functions: Vec<NodeId>,
}


impl<Facts: Hash + Eq + Clone> WorkQueue<Facts> {

    pub fn new<I: Iterator<Item=NodeId>>(functions: I) -> WorkQueue<Facts> {
        let mut q = WorkQueue {
            deps: KeyedDepGraph::new(),
            queue: VecDeque::new(),
            map: HashMap::new(),
            entered: HashSet::new(),
            functions: functions.collect(),
        };
        q.enqueue_user_cxs();
        q
    }

    /// Register that `self_cx` depends on `dep_cx` from basic block `origin`.
    /// This records the dependency so that when the analysis of `dep_cx` changes in the future,
    /// `self_cx` will be resubmitted to the queue, to be re-analyzed from `origin`.
    /// It also removes [0 or 1] old dependency of `self_cx` originating at `origin`. This include
    /// removing that depedency from the graph, and removing that origin from the queue.
    pub fn register_dependency(&mut self,
                               self_cx: &AnalysisUnit<Facts>,
                               dep_cx: AnalysisUnit<Facts>,
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
                              self_cx: &AnalysisUnit<Facts>) {
        for (dep, origins) in self.deps.get_dependents_with_keys(self_cx.clone()) {
            self.enqueue_many(dep, origins.into_iter())
        }
    }


    fn enqueue_many<O: Iterator<Item=BasicBlock>>(&mut self, au: AnalysisUnit<Facts>, origins: O) {
        if !self.entered.contains(&au) {
            self.map.insert(au.clone(), FlowSource::Returns);
            self.queue.push_back(au.clone());
            self.entered.insert(au);
        }
        else {
            if self.map.contains_key(&au) {
                match self.map.get_mut(&au).unwrap() {
                    &mut FlowSource::Blocks(ref mut blocks) => {
                        origins.map(|bb| blocks.insert(bb.clone())).count();
                    },
                    // If the item is already there with returns, it'll get this origin implicitly
                    _ => (),
                };
            } else {
                let mut set = HashSet::new();
                origins.map(|bb| set.insert(bb.clone())).count();
                self.map.insert(au.clone(), FlowSource::Blocks(set));
                self.queue.push_back(au);
            }
        }
    }

    pub fn enqueue_user_cxs(&mut self) {
        let fns = self.functions.clone();
        fns.iter().map(|other_id| self.enqueue_user_cx(other_id)).count();
    }

    fn enqueue_user_cx(&mut self, fn_nid: &NodeId) {
        let au = (*fn_nid, Context::User);
        if !self.map.contains_key(&au) {
            self.map.insert(au.clone(), FlowSource::Returns);
            self.queue.push_back(au.clone());
            self.entered.insert(au);
        }
    }

    pub fn get(&mut self) -> Option<WorkItem<Facts>> {
        self.queue.pop_back().map( |au| {
            let source = self.map.remove(&au).unwrap();
            // TODO. Make sure that the dependency still exists!
            WorkItem(au.0, au.1, source)
        })
    }
}

/// Flow that needs to be continued in some MIR.
///
/// The NodeId indicate which MIR, the Context indicates which facts should hold at returns, and
/// the FlowSource indicates where the flow should begin within the MIR.
pub struct WorkItem<Facts>(NodeId, Context<Facts>, FlowSource);

/// Where flow should begin in an MIR.
///
/// Either from the returns, or from specific blocks
pub enum FlowSource {
    Returns,
    Blocks(HashSet<BasicBlock>),
}

impl<'mir,'tcx, Facts, GlobalFacts> AnalysisState<'mir,'tcx,Facts,GlobalFacts>
    where Facts: Ord + Hash + Clone,
          GlobalFacts: Default {
    fn new(
       mir_map: &'mir MirMap<'tcx>,
       tcx: ty::TyCtxt<'mir,'tcx,'tcx>,
       access_levels: AccessLevels
    ) -> AnalysisState<'mir,'tcx,Facts,GlobalFacts> {
        AnalysisState {
            context_and_fn_to_fact_map: BTreeMap::new(),
            info: CrateInfo::new(mir_map, tcx, access_levels),
            queue: WorkQueue::new(mir_map.map.keys().map(|id| *id)),
            user_cx: GlobalFacts::default(),
        }
    }
}

impl<'mir,'tcx> CrateInfo<'mir,'tcx> {
    fn new(mir_map: &'mir MirMap<'tcx>,
           tcx: ty::TyCtxt<'mir,'tcx,'tcx>,
           access_levels: AccessLevels
    ) -> CrateInfo<'mir,'tcx> {
        CrateInfo {
            mir_map: mir_map,
            tcx: tcx,
            access_levels: access_levels
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

    // Taken from solson's MIRI:
    // https://github.com/solson/miri/blob/master/src/interpreter/terminator.rs
    //
    fn fulfill_obligation(&self, trait_ref: ty::PolyTraitRef<'tcx>) -> traits::Vtable<'tcx, ()> {
        // Do the initial selection for the obligation. This yields the shallow result we are
        // looking for -- that is, what specific impl.
        errln!("    Selection Begins: Trait Ref: {:?}", trait_ref);
        let dummy_sp = Span { lo: BytePos(0), hi: BytePos(0), expn_id: NO_EXPANSION };
        let res = self.tcx.normalizing_infer_ctxt(traits::ProjectionMode::Any).enter(|infcx| {
            let mut selcx = traits::SelectionContext::new(&infcx);

            let obligation = traits::Obligation::new(
                traits::ObligationCause::misc(dummy_sp, ast::DUMMY_NODE_ID),
                trait_ref.to_poly_trait_predicate(),
            );
            let raw_selection = selcx.select(&obligation);
            errln!("    Selection: {:?}", raw_selection);
            let selection = raw_selection.unwrap().unwrap();

            // Currently, we use a fulfillment context to completely resolve all nested
            // obligations.  This is because they can inform the inference of the impl's type
            // parameters.
            let mut fulfill_cx = traits::FulfillmentContext::new();
            let vtable = selection.map(|predicate| {
                fulfill_cx.register_predicate_obligation(&infcx, predicate);
            });
            infcx.drain_fulfillment_cx_or_panic(dummy_sp, &mut fulfill_cx, &vtable)
        });
        errln!("    Selection Result: {:?}", res);
        res
    }

    pub fn get_fn_ty(&self,
                     caller_node_id: &NodeId,
                     func_op: &Operand<'tcx>) -> &'tcx ty::BareFnTy<'tcx> {
        let caller_mir = self.node_id_to_mir(caller_node_id).expect("Callee MIR Node ID is bad");
        let op_ty = caller_mir.operand_ty(self.tcx, func_op);
        match op_ty.sty {
            TypeVariants::TyFnDef(_, _, bare_fn_ty) => bare_fn_ty,
            TypeVariants::TyFnPtr(bare_fn_ty) => bare_fn_ty,
            _ => bug!("Should be a function type!"),
        }
    }

    // If there is MIR for the value of this operand, this functions finds its ID (assuming the
    // operand is just constant) and precise type.
    //
    // Also took a lot of code from solson/miri
    pub fn get_fn_mir_id(&self,
                         caller_node_id: &NodeId,
                         func_op: &Operand<'tcx>) -> Option<NodeId> {
        // We start by looking up the type of the function_operand being called.
        let caller_mir = self.node_id_to_mir(caller_node_id).expect("Callee MIR Node ID is bad");
        let op_ty = caller_mir.operand_ty(self.tcx, func_op);
        let (resolved_def_id, _) = match op_ty.sty {
            // If this is a function pointer we can't figure out which MIR it refers to.
            ty::TyFnPtr(_) => return None,
            ty::TyFnDef(def_id, substs, _) => {
                if substs.self_ty().is_some() {
                    let method_item = self.tcx.impl_or_trait_item(def_id);
                    let trait_def_id = method_item.container().id();
                    let trait_ref = substs.to_trait_ref(self.tcx, trait_def_id);
                    match self.fulfill_obligation(ty::Binder(trait_ref)) {
                        traits::VtableImpl(vtable_impl_data) => {
                            let impl_def_id = vtable_impl_data.impl_def_id;
                            let impl_substs = vtable_impl_data.substs.with_method_from(substs);
                            let substs = self.tcx.mk_substs(impl_substs);
                            let method_name = self.tcx.item_name(def_id);
                            get_impl_method_def_id_and_substs(self.tcx, impl_def_id,
                                                              substs, method_name)
                        }
                        traits::VtableClosure(vtable_closure_data) => {
                            (vtable_closure_data.closure_def_id,
                             vtable_closure_data.substs.func_substs)
                        }
                        traits::VtableObject(_) |
                        traits::VtableFnPointer(_) => return None,
                        // TODO: Perhaps we can handle default impl's too?
                        // traits::VtableDefaultImpl
                        other_table => bug!("Unimplemented VTable option: {:#?}\nTy: {:#?}", other_table, op_ty.sty),
                    }
                }
                else {
                    (def_id, substs)
                }
            }
            _ => bug!("Not a function type!\n{:#?}\n{:#?}", func_op, op_ty.sty),
        };
        //errln!("    Type: {:?}", fn_ty);
        //self.get_fn_def_id(func_op).and_then(|def_id| {
        errln!("    Resolved Def {:?}", resolved_def_id);
        self.tcx.map.as_local_node_id(resolved_def_id)
        .and_then(|node_id| {
            errln!("    Node {:?}", node_id);
            if self.mir_map.map.contains_key(&node_id) {
                Some(node_id)
            }
            else { None }
        })
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

pub trait Facts : Default {
    // Produces the set of facts before a forward split in the CFG.
    fn join(&self, right: &Self) -> Self;

    fn join_many(many: Vec<&Self>) -> Self {
        many.into_iter().fold(Self::default(), |acc, item| acc.join(item))
    }
}

pub trait BackwardsAnalysis {
    //TODO: need so many bounds?
    type Facts: Hash + Debug + Ord + Default + Clone + Facts;
    type GlobalFacts: Debug + Clone + Eq + Facts;
    // The facts which are made by evaluating this expression. Comes up during some terminators.
    fn generate<'a, 'b, 'tcx: 'a + 'b + 'mir, 'mir, 'gcx: 'tcx>
        (mir_info: MIRInfo<'b, 'mir, 'gcx, 'tcx>, expr: Expr<'a, 'tcx>) -> Self::Facts;

    // Produces the set of facts before the execution of a statement.
    fn transfer<'a,'mir,'tcx:'a,'gcx:'tcx>(mir_info: MIRInfo<'a,'mir,'gcx,'tcx>,
                                           post_facts: &Self::Facts,
                                           statement: &StatementKind<'tcx>)
                                           -> Self::Facts;


    fn flow<'mir,'tcx>(mir_map: &'mir MirMap<'tcx>,
                       tcx: ty::TyCtxt<'mir,'tcx,'tcx>,
                       access_levels: AccessLevels)
                       -> AnalysisState<'mir,'tcx,Self::Facts,Self::GlobalFacts> {
        let mut state = AnalysisState::new(mir_map, tcx, access_levels);
        while let Some(work_item) = state.queue.get() {
            Self::flow_work_item(work_item, &mut state);
        }
        state
    }

    fn substantiate_au<'mir,'tcx>(
        state: &mut AnalysisState<Self::Facts,Self::GlobalFacts>,
        au: AnalysisUnit<Self::Facts>
    ) -> RawAnalysisUnit<Self::Facts>;

    /// Flows till convergence on a single (MIR,CX) - just looks up the results of other functions.
    /// Manipulates the state - changing (MIR,CX) dependencies and the queue.
    ///
    /// ## Returns
    fn flow_work_item<'mir,'tcx>(
        work_item: WorkItem<Self::Facts>,
        state: &mut AnalysisState<Self::Facts,Self::GlobalFacts>
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
        let true_au = (mir_id, context);
        let raw_au = Self::substantiate_au(state, true_au.clone());
        let cx_paths = raw_au.1.clone();
        let mir = state.info.mir_map.map.get(&mir_id).unwrap();
        let mir_info = state.info.get_mir_info(&mir_id);
        errln!("Pulling full ctx {:?}", true_au);
        let mut mir_facts = state.context_and_fn_to_fact_map.remove(&true_au)
            .unwrap_or(BTreeMap::new());

        // Initialize work queue with Basic Blocks from the flow source
        let mut bb_queue: VecDeque<BasicBlock> = VecDeque::new();
        match flow_source {
            FlowSource::Returns => {
                errln!("  BB Queue Initialized with all returns");
                for (bb_idx, bb_data) in traversal::postorder(&mir) {
                    use rustc::mir::repr::TerminatorKind::*;
                    //TODO: do Resume / Unreachable matter at all?
                    match bb_data.terminator().kind {
                        Return => bb_queue.push_front(bb_idx),
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
                    if !Self::apply_transfer(mir_id, &state.info, &mut mir_facts,
                                            pre_idx, post_idx, &assignment) {
                        new_flow = false;
                    }
                },
                // TODO handle non-static calls
                Call { destination: Some((ref lval, next_bb)), ref func, ref args, .. } => {
                    errln!("    Function: {:?}", func);
//                    if let &Operand::Constant(ref c) = func {
//                        write!(io::stderr(), "{}", json::as_json(&c.literal));
//                    }
                    let post_idx = StatementIdx(next_bb, 0);
                    let empty = Self::Facts::default();
                    let (maybe_dependency, new_pre_facts) =
                        Self::fn_call_transfer(mir_id, &state.info,
                                               &state.context_and_fn_to_fact_map,
                                               mir_facts.get(&post_idx).unwrap_or(&empty),
                                               func, args, lval);
                    if let Some(dep) = maybe_dependency {
                        errln!("    Dependency on {:?}, from {:?}", dep, bb_idx);
                        // We don't want to register dependencies on ourselves.
                        let dep = (dep.0, Context::Internal(dep.1));
                        if dep != true_au {
                            state.queue.register_dependency(&true_au, dep, bb_idx);
                        }
                    }

                    let change = mir_facts.remove(&pre_idx).map(|pre_facts|
                        pre_facts != new_pre_facts
                    ).unwrap_or(true);
                    if !change { new_flow = false; }
                    mir_facts.insert(pre_idx, new_pre_facts);
                },
                Return => {
                    let new_pre_facts = cx_paths.clone();
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
                                mir_facts.insert(post_idx, Self::Facts::default());
                            }
                        }
                        for succ_bb_idx in other.successors().iter() {
                            let post_idx = StatementIdx(*succ_bb_idx, 0);
                            post_facts.push(mir_facts.get(&post_idx).unwrap());
                        }
                        Self::Facts::join_many(post_facts)
                    };
                    let mir_info = state.info.get_mir_info(&mir_id);
                    evaluated_expression(other).map(|expr| {
                        new_pre_facts = new_pre_facts.join(&Self::generate(mir_info, expr))
                    });
                    let change = mir_facts.remove(&pre_idx).map(|pre_facts|
                        pre_facts != new_pre_facts
                    ).unwrap_or(true);
                    if !change { new_flow = false; }
                    mir_facts.insert(pre_idx, new_pre_facts);
                }
            }
            //errln!("    New Flow at Merge: {:?}", new_flow);
            if new_flow {
                for (s_idx, statement) in basic_block.statements.iter().enumerate().rev() {
                    let post_idx = StatementIdx(bb_idx, s_idx + 1);
                    let pre_idx = StatementIdx(bb_idx, s_idx);
                    //errln!("    Statement Idx: {:?}", pre_idx);
                    if !Self::apply_transfer(mir_id, &state.info, &mut mir_facts,
                                             pre_idx, post_idx, &statement.kind) {
                        new_flow = false;
                        break;
                    }
                }
            }
            //errln!("    New Flow at Start: {:?}", new_flow);
            if new_flow {
                mir.predecessors_for(bb_idx).iter().map(|pred_idx|
                    bb_queue.push_back(*pred_idx)
                ).count();
            }
            errln!("  BB Queue: {:?}", bb_queue);
        }

        if mir_facts.get(&START_STMT) != start_facts.as_ref() {
            // If our start facts changed, we've got to work on the dependencies
            state.queue.enqueue_dependents(&true_au);
        }

        // If we just did an analysis in the user context, then we potentially modify the user
        // context
        if true_au.1 == Context::User {
            let mut global = Self::extract_global_facts(mir_facts.get(&START_STMT).unwrap(), mir_info);
            global = global.join(&state.user_cx);
            if global != state.user_cx {
                state.queue.enqueue_user_cxs();
                //errln!("  New User Cx: {:?}", global);
                //errln!("         From: {:?}", state.user_cx);
                state.user_cx = global;
            }
        }
        errln!("Putting back ctx {:?}", true_au);
        //print_map_lines(&mir_facts);
        state.context_and_fn_to_fact_map.insert(true_au, mir_facts);
    }

    fn fn_call_transfer<'mir,'tcx>(mir_id: NodeId,
                                   crate_info: &CrateInfo<'mir,'tcx>,
                                   context_and_fn_to_fact_map: &CrateFactsMap<Self::Facts>,
                                   post_facts: &Self::Facts,
                                   fn_op: &Operand<'tcx>,
                                   arg_ops: &Vec<Operand<'tcx>>,
                                   dest: &Lvalue<'tcx>)
                                   -> (Option<RawAnalysisUnit<Self::Facts>>, Self::Facts);

    /// Apply the transfer function across this statment, which must lie between the two indices.
    /// Returns whether or not the facts for `pre_idx` actually changed because of the transfer
    /// function, so that the caller can detect when the flow stabilizes.
    fn apply_transfer<'mir,'gcx,'tcx>(mir_id: NodeId,
                                      crate_info: &CrateInfo<'mir,'tcx>,
                                      mir_facts: &mut MIRFactsMap<Self::Facts>,
                                      pre_idx: StatementIdx,
                                      post_idx: StatementIdx,
                                      statement: &StatementKind<'tcx>)
                                      -> bool {
        let new_pre_facts = {
            let post_facts = mir_facts.entry(post_idx).or_insert_with(Self::Facts::default);
            let mir_info = crate_info.get_mir_info(&mir_id);
            Self::transfer(mir_info, post_facts, statement)
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

    fn extract_global_facts<'a, 'mir, 'gcx: 'tcx, 'tcx: 'mir + 'a>(
        entry_facts: &Self::Facts,
        mir_info: MIRInfo<'a, 'mir, 'tcx, 'gcx>
    ) -> Self::GlobalFacts;
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

// Taken from solson/miri
/// Locates the applicable def_id and substs of a method, given its name and the impl def_id.
fn get_impl_method_def_id_and_substs<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    impl_def_id: DefId,
    substs: &'tcx ty::subst::Substs<'tcx>,
    name: ast::Name,
) -> (DefId, &'tcx ty::subst::Substs<'tcx>) {
    use rustc::ty::TypeFoldable;
    assert!(!substs.types.needs_infer());

    let trait_def_id = tcx.trait_id_of_impl(impl_def_id).unwrap();
    let trait_def = tcx.lookup_trait_def(trait_def_id);

    match trait_def.ancestors(impl_def_id).fn_defs(tcx, name).next() {
        Some(node_item) => {
            let substs = tcx.normalizing_infer_ctxt(traits::ProjectionMode::Any).enter(|infcx| {
                let substs = traits::translate_substs(&infcx, impl_def_id,
                                                      substs, node_item.node);
                tcx.lift(&substs).unwrap_or_else(|| {
                    bug!("trans::meth::get_impl_method: translate_substs \
                          returned {:?} which contains inference types/regions",
                         substs);
                })
            });
            (node_item.item.def_id, substs)
        }
        None => {
            bug!("method {:?} not found in {:?}", name, impl_def_id)
        }
    }
}
