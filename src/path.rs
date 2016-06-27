#![allow(dead_code)]
use base_var::BaseVar;

use std::collections::HashSet;

use rustc::mir::repr::{CastKind,
                       Constant,
                       Lvalue,
                       LvalueProjection,
                       Operand,
                       ProjectionElem,
                       Mir,
                       Rvalue,
};

use rustc::ty::{TypeVariants,
                TypeAndMut,
                AdtDefData,
                TyCtxt,
};

use rustc_data_structures::indexed_vec::Idx;
use std::collections::BTreeSet;
use std::fmt::{self,Formatter};

/// A critical path, including the path and why it's critical
#[derive(Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub struct CriticalPath {
    path: Path,
    ty: CriticalUse,
}

impl CriticalPath {
    pub fn new(path: Path, ty: CriticalUse) -> CriticalPath {
        CriticalPath { path: path, ty: ty }
    }
    pub fn deref(path: Path) -> CriticalPath {
        CriticalPath::new(path, CriticalUse::Deref)
    }
    pub fn value(path: Path) -> CriticalPath {
        CriticalPath::new(path, CriticalUse::Value)
    }

    pub fn is_deref(&self) -> bool {
        match self.ty {
            CriticalUse::Deref => true,
            CriticalUse::Value => false,
        }
    }

    /// `from` has been assigned to `to`. Take self and do the ppath substitution if possible,
    /// otherwise leave self unchanged.
    pub fn sub_if_possible(mut self, from: &Path, to: &Path) -> CriticalPath {
        let new_path = self.path.sub(from, to);
        if let Some(new_path) = new_path {
            self.path = new_path;
        }
        self
    }

    /// `from` is being replaced with `&to`. As long as `from` itself is recorded as safe to Deref,
    /// this is equivalent to replacing `*from` with `to`. if `from.#` ever appears (rather than
    /// `*from`, then something weird is going on. No address can be stored in a location with
    /// fields (I think)
    pub fn sub_ref_if_possible(self, from: &Path, to: &Path) -> CriticalPath {
        let expanded_from = from.clone().add_projection(Projection::Deref);
        if self.contains(from) {
            if self.contains(&expanded_from) {
                self.sub_if_possible(&expanded_from, to)
            } else {
                panic!("Tried to do `{:?} = &{:?}`, but found fact {:?}", from, to, self);
            }
        } else { self }
    }

    /// `from` has been assigned to computation of `to` which is not well-define on paths (such as
    /// addition, negation, etc. If self is affected, then replace is with a value dependence on
    /// `from`.
    ///
    /// I.E. if `*p` were deref'd after `*p = -(*x)`, then before the assignment the value of `*x`
    /// should be critical.
    pub fn downgrade_if_needed(self, from: &Path, to: &Path) -> CriticalPath {
        if self.path.contains(from) {
            CriticalPath::value(to.clone())
        } else { self }
    }

    pub fn seccure_for_deref(self, safe_to_deref: Path) -> Option<CriticalPath> {
        let secure = CriticalPath::deref(safe_to_deref);
        if self == secure { None } else { Some(self) }
    }

    pub fn contains(&self, other: &Path) -> bool {
        self.path.contains(other)
    }

    pub fn base(&self) -> &BaseVar {
        &self.path.base
    }

    /// Returns whether or not this CriticalPath involves an argument
    pub fn of_argument(&self) -> bool {
        if let BaseVar::Arg(_) = self.path.base { true } else { false }
    }

    /// Returns whether or not this CriticalPath involves the return pointer
    pub fn of_return_pointer(&self) -> bool {
        self.path.base == BaseVar::ReturnPointer
    }
}

impl fmt::Display for CriticalPath {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl fmt::Debug for CriticalPath {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.ty {
            CriticalUse::Deref => write!(f, "Deref({})", &self.path),
            CriticalUse::Value => write!(f, "Value({})", &self.path),
        }
    }
}

#[derive(Debug,Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub enum CriticalUse {
    /// This value is dereferenced.
    Deref,

    /// This value is somehow important - cannot be sunk.
    Value,
}

#[derive(Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub struct Path {
    pub projections: Vec<Projection>,
    pub base: BaseVar,
}

#[derive(Debug,Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub enum Projection {
    Deref,
    Field(usize),
}

impl Projection {
    pub fn is_deref(&self) -> bool {
        match *self {
            Projection::Deref => true,
            Projection::Field(_) => false
        }
    }
}

impl Path {
    pub fn from_base_var(base: BaseVar) -> Path {
        Path { projections: vec![], base: base }
    }

    pub fn add_projection(mut self, p: Projection) -> Path {
        self.projections.push(p);
        self
    }

    pub fn strip_highest_deref(mut self) -> Option<Path> {
        let index = self.projections.iter().rposition(|proj| proj.is_deref());
        index.map(|index| {
            self.projections.remove(index);
            self
        })
    }

    pub fn sub(&self, from: &Path, to: &Path) -> Option<Path> {
        if self.base == from.base {
            if self.projections.starts_with(from.projections.as_slice()) {
                let mut new = to.clone();
                let rest_of_original = &self.projections.as_slice()[from.projections.len()..];
                new.projections.extend_from_slice(rest_of_original);
                Some(new)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn contains(&self, other: &Path) -> bool {
        (self.base == other.base) && self.projections.starts_with(other.projections.as_slice())
    }

    pub fn sub_if_possible(self, from: &Path, to: &Path) -> Path {
        self.sub(from, to).unwrap_or(self)
    }
}
impl fmt::Debug for Path {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for projection in self.projections.iter() {
            match *projection {
                Projection::Deref => try!(write!(f, "*(")),
                Projection::Field(_) => try!(write!(f, "(")),
            }
        }
        try!(write!(f, "{:?}", self.base));
        for projection in self.projections.iter().rev() {
            match *projection {
                Projection::Deref => try!(write!(f, ")")),
                Projection::Field(idx) => try!(write!(f, ".{})", idx)),
            }
        }
        write!(f, "")
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// The paths that are assumed to be valid by reading / writing to this lvalue.
/// The last path in the vector is the actual path of the lvalue.
pub fn assumed_valid_by_lvalue(lvalue: &Lvalue) -> Vec<Path> {
    let mut with_base = _assumed_valid_by_lvalue(lvalue);
    with_base.retain(|path| path.projections.len() > 0);
    with_base
}
fn _assumed_valid_by_lvalue(lvalue: &Lvalue) -> Vec<Path> {
    use rustc::mir::repr::Lvalue::*;
    match *lvalue {
        Var(v) => vec![Path::from_base_var(BaseVar::Var(v))],
        Temp(v) => vec![Path::from_base_var(BaseVar::Temp(v))],
        Arg(v) => vec![Path::from_base_var(BaseVar::Arg(v))],
        Static(v) => vec![Path::from_base_var(BaseVar::Static(v))],
        ReturnPointer => vec![Path::from_base_var(BaseVar::ReturnPointer)],
        Projection(box ref lvalue_proj) => _assumed_valid_by_lvalue_projection(lvalue_proj),
    }
}

/// The paths that are assumed to be valid by reading / writing this projection.
/// The last path in the vector is the actual path of the projection.
pub fn assumed_valid_by_lvalue_projection(lvalue_proj: &LvalueProjection) -> Vec<Path> {
    let mut with_base = _assumed_valid_by_lvalue_projection(lvalue_proj);
    with_base.retain(|path| path.projections.len() > 0);
    with_base
}
fn _assumed_valid_by_lvalue_projection(lvalue_proj: &LvalueProjection) -> Vec<Path> {
    use rustc::mir::repr::ProjectionElem::*;
    let LvalueProjection{ ref base, ref elem } = *lvalue_proj;
    let mut paths_assumed_by_subexprs = _assumed_valid_by_lvalue( base );
    let path_assumed_by_this_expr = {
        let base_path = paths_assumed_by_subexprs[paths_assumed_by_subexprs.len() - 1].clone();
        match *elem {
            Deref | Index(_) | ConstantIndex { .. } | Subslice { .. } =>
                Some(base_path.add_projection(Projection::Deref)),
            Field(field_idx, _) =>
                Some(base_path.add_projection(Projection::Field(field_idx.index()))),
            // TODO: Sum Types?
            _ => None
        }
    };
    path_assumed_by_this_expr.map(|path| paths_assumed_by_subexprs.push(path));
    paths_assumed_by_subexprs
}

/// The paths that are assumed to be valid by reading / writing to this operand.
/// The last path in the vector is the actual path of the rvalue.
pub fn assumed_valid_by_operand(operand: &Operand) -> Vec<Path> {
    let mut with_base = _assumed_valid_by_operand(operand);
    with_base.retain(|path| path.projections.len() > 0);
    with_base
}
fn _assumed_valid_by_operand(operand: &Operand) -> Vec<Path> {
    use rustc::mir::repr::Operand::*;
    match *operand {
        Consume(ref lvalue) => _assumed_valid_by_lvalue(lvalue),
        // TODO: We know constants are safe, right?
        Constant(_) => vec![]
    }
}

/// The paths that are assumed to be valid by reading / writing to this rvalue.
/// The last path in the vector is the actual path of the rvalue.
pub fn assumed_valid_by_rvalue(rvalue: &Rvalue) -> Vec<Path> {
    let mut with_base = _assumed_valid_by_rvalue(rvalue);
    with_base.retain(|path| path.projections.len() > 0);
    with_base
}
fn _assumed_valid_by_rvalue(rvalue: &Rvalue) -> Vec<Path> {
    use rustc::mir::repr::Rvalue::*;
    match *rvalue {
        Use(ref operand) | Repeat(ref operand, _) | Cast(CastKind::Misc, ref operand, _) |
            UnaryOp(_, ref operand) | Cast(_, ref operand, _) =>
            _assumed_valid_by_operand(operand),
        //TODO: does &*p assume *p is valid? Seems to optimize it out, so no...
        Ref(_, _, ref lvalue) => {
            let _assumed_by_subexprs = _assumed_valid_by_lvalue(lvalue);
            _assumed_by_subexprs.into_iter().filter_map(|path| path.strip_highest_deref()).collect()
        },
        Len(ref lvalue) => _assumed_valid_by_lvalue(lvalue),
        Aggregate(_, ref ops) => 
            ops.iter().map(|op| _assumed_valid_by_operand(op))
                      .fold(vec![],|mut v, e| {v.extend(e); v}),
        Box(_) => vec![],
        BinaryOp(_, ref o1, ref o2) | CheckedBinaryOp(_, ref o1, ref o2) => {
            let mut paths = _assumed_valid_by_operand(o1);
            paths.extend(_assumed_valid_by_operand(o2));
            paths
        },
        InlineAsm{ .. } => { unimplemented!(); },
    }
}


/// The path an Lvalue refers to
pub fn lvalue_path(lvalue: &Lvalue) -> Path {
    use rustc::mir::repr::Lvalue::*;
    match *lvalue {
        Var(v) => Path::from_base_var(BaseVar::Var(v)),
        Temp(v) => Path::from_base_var(BaseVar::Temp(v)),
        Arg(v) => Path::from_base_var(BaseVar::Arg(v)),
        Static(v) => Path::from_base_var(BaseVar::Static(v)),
        ReturnPointer => Path::from_base_var(BaseVar::ReturnPointer),
        Projection(box ref lvalue_proj) => lvalue_projection_path(lvalue_proj),
    }
}

/// The path for an Lvalue
pub fn lvalue_projection_path(lvalue_proj: &LvalueProjection) -> Path {
    use rustc::mir::repr::ProjectionElem::*;
    let LvalueProjection{ ref base, ref elem } = *lvalue_proj;
    let base_path = lvalue_path(base);
    match *elem {
        Deref | Index(_) | ConstantIndex { .. } | Subslice { .. } =>
            base_path.add_projection(Projection::Deref),
        Field(field_idx, _) =>
            base_path.add_projection(Projection::Field(field_idx.index())),
        // TODO: Sum Types?
        _ => base_path,
    }
}

/// The path for an operand. If the operand is a constant then no path is returned.
pub fn operand_path(operand: &Operand) -> Option<Path> {
    use rustc::mir::repr::Operand::*;
    match *operand {
        Consume(ref lvalue) => Some(lvalue_path(lvalue)),
        // TODO: We know constants are safe, right?
        Constant(_) => None
    }
}

/// The path for an rvalue. If the rvalue is a constant then no path is returned.
pub fn rvalue_path(rvalue: &Rvalue) -> Option<Path> {
    use rustc::mir::repr::Rvalue::*;
    match *rvalue {
        Use(ref operand) | Repeat(ref operand, _) | Cast(CastKind::Misc, ref operand, _) |
            Cast(_, ref operand, _) =>
            operand_path(operand),
        Ref(_, _, _) => bug!("Don't call rvalue_path on a Ref operation!"),
        Aggregate(_, ref ops) => {
            if ops.iter().all(|op| operand_path(op).is_none()) { None }
            else { unimplemented!() }
        },
        UnaryOp(_, _) | BinaryOp(_, _, _) | CheckedBinaryOp(_, _, _) | Box(_) | Len(_) => None,

        InlineAsm { .. } => {
            unimplemented!();
        },
    }
}

pub fn transfer_and_gen_paths_assign(
    post_paths: &HashSet<Path>,
    lvalue: &Lvalue,
    rvalue: &Rvalue) -> HashSet<Path> {
    let mut pre_paths = just_transfer_paths_assign(post_paths, lvalue, rvalue);
    pre_paths.extend(assumed_valid_by_lvalue(lvalue));
    pre_paths.extend(assumed_valid_by_rvalue(rvalue));
    pre_paths
}

/// TODO: Enter the exaplanation from notebook.
pub fn constant_assignment<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                             tcx: TyCtxt<'mir, 'gcx, 'tcx>,
                                             post_paths: &HashSet<CriticalPath>,
                                             l_path: &Path,
                                             constant: &Constant)
                                             -> HashSet<CriticalPath> {
    post_paths.iter().filter(|p| !p.contains(l_path)).cloned().collect()
}

pub fn operand_assignment<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                            tcx: TyCtxt<'mir, 'gcx, 'tcx>,
                                            post_paths: &HashSet<CriticalPath>,
                                            l_path: &Path,
                                            operand: &Operand)
                                            -> HashSet<CriticalPath> {
    match *operand {
        Operand::Consume(ref r_lvalue) => {
            let r_path = lvalue_path(r_lvalue);
            post_paths.iter().cloned()
                .map(|path| path.sub_if_possible(l_path, &r_path)).collect()
        },
        Operand::Constant(ref constant) =>
            constant_assignment(mir, tcx, post_paths, l_path, constant),
    }
}

/// When `l = C
pub fn assignment_downgrade<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                              tcx: TyCtxt<'mir, 'gcx, 'tcx>,
                                              post_paths: &HashSet<CriticalPath>,
                                              lvalue: &Lvalue,
                                              operand: &Operand)
                                              -> HashSet<CriticalPath> {
    let l_path = lvalue_path(lvalue);
    match *operand {
        Operand::Consume(ref r_lvalue) => {
            let r_path = lvalue_path(r_lvalue);
            post_paths.iter().cloned()
                .map(|path| path.downgrade_if_needed(&l_path, &r_path)).collect()
        },
        Operand::Constant(ref constant) =>
            constant_assignment(mir, tcx, post_paths, &l_path, constant),
    }
}

pub fn just_sub_paths<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                        tcx: TyCtxt<'mir, 'gcx, 'tcx>,
                                        post_paths: &HashSet<CriticalPath>,
                                        lvalue: &Lvalue<'tcx>,
                                        rvalue: &Rvalue<'tcx>)
                                        -> HashSet<CriticalPath> {

    use rustc::mir::repr::Rvalue::*;
    use rustc::ty::TypeVariants::*;

    let l_path = lvalue_path(lvalue);
    match *rvalue {
        Use(ref operand) |
        Repeat(ref operand, _) => operand_assignment(mir, tcx, post_paths, &l_path, operand),
        Cast(_, ref operand, ref ty) => {
            let ref from_sty = mir.operand_ty(tcx, operand).sty;
            let ref to_sty = ty.sty;
            // Build a set of paths with any paths seccured by the cast removed (`y: * = x: &`
            // secures *y).
            let mut ref_seccured_paths = post_paths.clone();
            match (from_sty, to_sty) {
                (&TyRef(_, _), &TyRawPtr(_)) => {
                    let seccured_path = CriticalPath::deref(l_path.clone());
                    ref_seccured_paths.remove(&seccured_path);
                },
                _ => { },
            };
            operand_assignment(mir, tcx, &ref_seccured_paths, &l_path, operand)
        },

        UnaryOp(_, ref operand) => {
            assignment_downgrade(mir, tcx, post_paths, lvalue, operand)
        }

        BinaryOp(_, ref o1, ref o2) |
        CheckedBinaryOp(_, ref o1, ref o2) => {
            let mut v = assignment_downgrade(mir, tcx, post_paths, lvalue, o1);
            v.extend(assignment_downgrade(mir, tcx, post_paths, lvalue, o2));
            v
        }

        Ref(_, _, ref lvalue) => {
            let r_path = lvalue_path(lvalue);
            let seccured_path = CriticalPath::deref(r_path.clone());
            post_paths.iter().filter(|path| **path != seccured_path ).cloned()
                .map(|path| path.sub_ref_if_possible(&l_path, &r_path)).collect()
        }
        Len(ref lvalue) => {
            let r_path = lvalue_path(lvalue);
            post_paths.iter().cloned()
                .map(|path| path.downgrade_if_needed(&l_path, &r_path)).collect()
        },

        // P = (Q1, Q2, ...)
        // Post: Facts
        Aggregate(_, ref operands) => {
            let mut pre_paths = post_paths.clone();
            // Find all P.i in Facts, and do `P.i = Qi`
            for (idx, op) in operands.iter().enumerate() {
                let l_path_i = l_path.clone().add_projection(Projection::Field(idx));
                pre_paths = match *op {
                    Operand::Consume(ref r_lvalue) => {
                        let r_path = lvalue_path(r_lvalue);
                        pre_paths.into_iter()
                            .map(|path| path.sub_if_possible(&l_path_i, &r_path)).collect()
                    },
                    Operand::Constant(ref constant) => {
                        constant_assignment(mir, tcx, &pre_paths, &l_path, constant)
                    },
                }
            }
            // Find all P in Facts, and do, for all i, `P.i = Qi; ...`, downgrading.
            // The reason we downgrade is that if P need to be derefd, but is potentially unsafe to
            // be so, then it must be turned into a raw ptr at some point? This is _real_ weird.
            pre_paths.into_iter().flat_map(|crit_path| {
                if crit_path.contains(&l_path) {
                    panic!("Aggregate assigned to a path which needed to be deref'd safetly");
//                    operands.iter().enumerate().map(|(idx, op)| {
//                        let l_path_i = l_path.add_projection(Projection::Field(idx));
//                        let r_path = operand_path(op);
//                        crit_path.downgrade_if_needed(l_path_i, r_path)
//                    }).collect::<Vec<_>>()
                } else {
                    vec![crit_path]
                }
            }).collect()
        },
        InlineAsm { .. } => unimplemented!(),
        Box(_) => unimplemented!(),
    }
}
pub fn just_transfer_paths_assign(
    post_paths: &HashSet<Path>,
    lvalue: &Lvalue,
    rvalue: &Rvalue) -> HashSet<Path> {

    use rustc::mir::repr::Rvalue::*;
    let l_path = lvalue_path(lvalue);
    match *rvalue {
        Ref(_, _, ref rlvalue) => {
            let rl_path = lvalue_path(rlvalue);
            let rvalue = &Use(Operand::Consume(rlvalue.clone()));
            let l_for_rl = just_transfer_paths_assign(post_paths, lvalue, &rvalue);
            l_for_rl.into_iter().filter_map(|path| {
                if path.base == rl_path.base {
                    path.strip_highest_deref()
                } else {
                    Some(path)
                }
            }).collect()
        },
        ref rvalue => {
            let other_base_paths =
                    post_paths.iter().filter(|post_path| post_path.base != l_path.base).cloned();
            if post_paths.iter().any(|path| path.base == l_path.base) {
                match rvalue_path(rvalue) {
                    // If r_value is a path (not a constant) then substitute r_paths for l_paths
                    Some(r_path) =>
                        other_base_paths.chain(post_paths.iter().filter_map(|post_path|
                            post_path.sub(&l_path, &r_path)
                        )).collect(),
                    None => other_base_paths.collect(),
                }
            } else {
                other_base_paths.collect()
            }
        },
    }
}

pub fn gen_by_operand<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                            tcx: TyCtxt<'mir, 'gcx, 'tcx>,
                                            operand: &Operand<'tcx>)
                                            -> Vec<CriticalPath> {
    use rustc::mir::repr::Operand::*;
    match operand {
        &Consume(ref lvalue) => gen_by_lvalue(mir, tcx, lvalue),
        //Constants contain no projections - definitely safe.
        &Constant(_) => vec![],
    }
}

pub fn gen_by_lvalue<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                           tcx: TyCtxt<'mir, 'gcx, 'tcx>,
                                           lvalue: &Lvalue<'tcx>)
                                           -> Vec<CriticalPath> {
    match lvalue {
        &Lvalue::Projection(box LvalueProjection { ref base, ref elem }) => {
            let mut v = gen_by_lvalue(mir, tcx, base);
            match elem {
                &ProjectionElem::Deref => {
                    let base_ty = mir.lvalue_ty(tcx, base);
                    if let TypeVariants::TyRawPtr(_) = base_ty.to_ty(tcx).sty {
                        v.push(CriticalPath::deref(lvalue_path(base)))
                    }
                },
                // TODO: Do we want to handle OoB on arrays?
                _ => (),
            };
            v
        },
        _ => vec![],
    }
}

pub fn gen_by_rvalue<'tcx, 'mir, 'gcx>(mir: &Mir<'tcx>,
                                       tcx: TyCtxt<'mir, 'gcx, 'tcx>,
                                       rvalue: &Rvalue<'tcx>)
                                       -> Vec<CriticalPath> {
    use rustc::mir::repr::Rvalue::*;
    match *rvalue {
        Use(ref operand) |
        Repeat(ref operand, _) |
        Cast(_, ref operand, _) |
        UnaryOp(_, ref operand) => gen_by_operand(mir, tcx, operand),

        BinaryOp(_, ref o1, ref o2) |
        CheckedBinaryOp(_, ref o1, ref o2) => {
            let mut v = gen_by_operand(mir, tcx, o1);
            v.extend(gen_by_operand(mir, tcx, o2));
            v
        }

        Ref(_, _, ref lvalue) |
        Len(ref lvalue) => gen_by_lvalue(mir, tcx, lvalue),

        Aggregate(_, ref operands) => {
            let mut v = vec![];
            operands.iter().map(|o| v.extend(gen_by_operand(mir, tcx, o))).count();
            v
        },
        InlineAsm { .. } => unimplemented!(),
        Box(_) => vec![],
    }
}

fn is_path_valid_for_type<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, sty: &TypeVariants<'tcx>, path: &Path) -> bool {
    // We walk through each operation performed by the projection, looking at the types produced,
    // and verifying that each operation of the projection can be performed on that type.
    let mut current_type = sty;
    use rustc::ty::TypeVariants::*;
    for projection in path.clone().projections {
        println!("Ty {:?}", current_type);
        match *current_type {
            TyRawPtr(TypeAndMut{ ref ty, .. }) => {return false;},
            TyRef(_, TypeAndMut{ ref ty, .. }) => {
                if let Projection::Deref = projection {
                    current_type = &ty.sty;
                } else { panic!("Type system broken") }
            },
            TyStruct(ref adt_def, ref substs) => {
                if let Projection::Field(idx) = projection {
                    let field = adt_def.struct_variant().fields.get(idx).expect("Ty Sys broken");
                    current_type = &field.ty(tcx, substs).sty;
                } else { panic!("Type system broken") }
            }
            TyTuple(ref fields) => {
                if let Projection::Field(idx) = projection {
                    if idx < fields.len() {
                        current_type = &fields[idx].sty;
                    } else { panic!("Type system broken") }
                } else { panic!("Type system broken") }
            },
            _ => {panic!("Type system broken");},
        }
    }
    true //TODO
}

#[test]
fn test_assumed_by_operand_constant() {
    use rustc::mir::repr::*;
    let operand = Operand::Consume(Lvalue::Var(Var::new(0)));
    let actual_facts: BTreeSet<_> = assumed_valid_by_operand(&operand).into_iter().collect();
    let expected_facts: BTreeSet<_> = vec![].into_iter().collect();
    assert_eq!(actual_facts, expected_facts);
}

#[test]
fn test_assumed_by_operand_deref_constant() {
    use rustc::mir::repr::*;
    let projection = Projection { base: Lvalue::Var(Var::new(0)), elem: ProjectionElem::Deref };
    let operand = Operand::Consume(Lvalue::Projection(box projection));
    let actual_facts: BTreeSet<_> = assumed_valid_by_operand(&operand).into_iter().collect();
    let expected_facts: BTreeSet<_> = vec![Path::from_base_var(BaseVar::Var(Var::new(0))).add_projection(self::Projection::Deref)].into_iter().collect();
    assert_eq!(actual_facts, expected_facts);
}

#[test]
fn test_assumed_by_lvalue_constant() {
    use rustc::mir::repr::*;
    let lvalue = Lvalue::Var(Var::new(0));
    let actual_facts: BTreeSet<_> = assumed_valid_by_lvalue(&lvalue).into_iter().collect();
    let expected_facts: BTreeSet<_> = vec![].into_iter().collect();
    assert_eq!(actual_facts, expected_facts);
}

#[test]
fn test_assumed_by_lvalue_deref_constant() {
    use rustc::mir::repr::*;
    let projection = Projection { base: Lvalue::Var(Var::new(0)), elem: ProjectionElem::Deref };
    let operand = Lvalue::Projection(box projection);
    let actual_facts: BTreeSet<_> = assumed_valid_by_lvalue(&operand).into_iter().collect();
    let expected_facts: BTreeSet<_> = vec![Path::from_base_var(BaseVar::Var(Var::new(0))).add_projection(self::Projection::Deref)].into_iter().collect();
    assert_eq!(actual_facts, expected_facts);
}
