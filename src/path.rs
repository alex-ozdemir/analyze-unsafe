#![allow(dead_code)]
use base_var::BaseVar;

use std::collections::HashSet;

use rustc::mir::repr::{CastKind,
                       Lvalue,
                       LvalueProjection,
                       Operand,
                       Rvalue,
};

use rustc::ty::TypeVariants;

use rustc_data_structures::indexed_vec::Idx;
use std::collections::BTreeSet;

#[derive(Debug,Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
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

    pub fn substitute(&self, from: &Path, to: &Path) -> Option<Path> {
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
                            post_path.substitute(&l_path, &r_path)
                        )).collect(),
                    None => other_base_paths.collect(),
                }
            } else {
                other_base_paths.collect()
            }
        },
    }
}

fn is_path_valid_for_type<'tcx>(sty: &TypeVariants<'tcx>, path: &Path) -> bool {
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
