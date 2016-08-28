use path::{Path,Projection,TmpPath,TmpProjection,Projectable};
use base_var::BaseVar;
use backflow::MIRInfo;

use std::iter::{FromIterator,IntoIterator};

use rustc::mir::repr::{
    Lvalue,
    LvalueProjection,
    Operand,
    ProjectionElem,
    StatementKind,
    Rvalue,
};

use rustc_data_structures::indexed_vec::Idx;

use std::mem;
use std::collections::{BTreeSet,BTreeMap,btree_map};
use std::fmt::Debug;

const MAX_PATH_LEN: usize = 10;

/// A critical path, including the path and why it's critical
#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub struct CriticalPaths<Base: Clone + Ord> {
    map: BTreeMap<Path<Base>, CriticalUse>,
}

impl<Base: Clone + Ord> Default for CriticalPaths<Base> {
    fn default() -> CriticalPaths<Base> {
        CriticalPaths {
            map: BTreeMap::default()
        }
    }
}

impl<Base: Clone + Ord> CriticalPaths<Base> {
    pub fn empty() -> Self {
        CriticalPaths { map: BTreeMap::new() }
    }

    /// Insert this (path, use) into the set of facts.
    /// This handles a number of subtleties:
    ///    1. If the path is too long it will be truncated to a shorter `Value` path
    ///    2. If the path is implied by an existing `Value` path it will not be inserted.
    ///    3. If the path is a `Value` path and implies existing paths, they will be removed.
    pub fn insert(&mut self, mut path: Path<Base>, mut u: CriticalUse) {
        if path.truncate(MAX_PATH_LEN) {
            u = CriticalUse::Value;
        }
        let implied_by_existing = self.map.iter().any(|(p2, u2)| {
            (u2 == &CriticalUse::Value) && path.contains(p2)
        });
        if !implied_by_existing {
            if u == CriticalUse::Value {
                let tmp_map = mem::replace(&mut self.map, BTreeMap::new());
                for (p2, u2) in tmp_map.into_iter().filter(|&(ref p2, _)| !p2.contains(&path)) {
                    self.map.insert(p2, u2);
                }
            }
            self.map.insert(path, u);
        }
    }
    pub fn get(&self, p: &Path<Base>) -> Option<&CriticalUse> {
        self.map.get(p)
    }
    pub fn keys<'a>(&'a self) -> btree_map::Keys<'a,Path<Base>,CriticalUse> {
        self.map.keys()
    }
    pub fn remove(&mut self, path: &Path<Base>, u: &CriticalUse) {
        if self.map.get(path) == Some(u) {
            self.map.remove(path);
        }
    }
    pub fn iter(&self) -> btree_map::Iter<Path<Base>,CriticalUse> {
        self.map.iter()
    }
    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn replace_base(&mut self, b: &Base, new: Path<Base>) {
        mem::replace(self, Self::empty()).into_iter().map(|(mut path, u)| {
            path.replace_base(b, new.clone());
            self.insert(path, u);
        }).count();
    }
}

impl<Base: Clone + Ord> IntoIterator for CriticalPaths<Base> {
    type Item = (Path<Base>, CriticalUse);
    type IntoIter = btree_map::IntoIter<Path<Base>, CriticalUse>;
    fn into_iter(self) -> btree_map::IntoIter<Path<Base>, CriticalUse> {
        self.map.into_iter()
    }
}

impl<Base: Clone + Ord> FromIterator<(Path<Base>, CriticalUse)> for CriticalPaths<Base>
    where Path<Base>: Ord {
    fn from_iter<T>(iter: T) -> CriticalPaths<Base>
        where T: IntoIterator<Item=(Path<Base>, CriticalUse)> {
        let mut paths = CriticalPaths::empty();
        paths.extend(iter.into_iter());
        paths
    }
}

impl<Base: Clone + Ord> Extend<(Path<Base>, CriticalUse)> for CriticalPaths<Base> {
    fn extend<T>(&mut self, iter: T)
        where T: IntoIterator<Item=(Path<Base>, CriticalUse)> {
        for (path, u) in iter {
            self.insert(path, u);
        }
    }
}

pub type Fact<Base> = (Path<Base>, CriticalUse);

#[derive(Debug,Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub enum CriticalUse {
    /// This value is dereferenced.
    Deref,

    /// This value is somehow important.
    /// This is a very general statement, so it's hard to 'sink' this critical use.
    Value,
}

/// The path an Lvalue refers to
pub fn lvalue_path(lvalue: &Lvalue) -> Path<BaseVar> {
    use rustc::mir::repr::Lvalue::*;
    match *lvalue {
        Var(v) => Path::from_base(BaseVar::Var(v)),
        Temp(v) => Path::from_base(BaseVar::Temp(v)),
        Arg(v) => Path::from_base(BaseVar::Arg(v)),
        Static(v) => Path::from_base(BaseVar::Static(v)),
        ReturnPointer => Path::from_base(BaseVar::ReturnPointer),
        Projection(box ref lvalue_proj) => lvalue_projection_path(lvalue_proj),
    }
}

/// The path for an Lvalue
pub fn lvalue_projection_path(lvalue_proj: &LvalueProjection) -> Path<BaseVar> {
    use rustc::mir::repr::ProjectionElem::*;
    let LvalueProjection{ ref base, ref elem } = *lvalue_proj;
    let mut base_path = lvalue_path(base);
    match *elem {
        Deref =>
            base_path.add_projection_in_place(Projection::Deref),
        Field(field_idx, _) => base_path.field_in_place(field_idx.index()),
        Downcast(_, variant_idx) => base_path.downcast_in_place(variant_idx),
        Index(_) | ConstantIndex { .. } | Subslice { .. } => (),
    };
    base_path
}

/// The path for an operand. If the operand is a constant then no path is returned.
pub fn operand_path(operand: &Operand) -> Option<Path<BaseVar>> {
    use rustc::mir::repr::Operand::*;
    match *operand {
        Consume(ref lvalue) => Some(lvalue_path(lvalue)),
        // TODO: We know constants are safe, right?
        Constant(_) => None
    }
}

pub fn join_many<'a, Base: 'a + Clone + Ord, I: Iterator<Item=&'a CriticalPaths<Base>>>(
    iter: I
) -> CriticalPaths<Base> {
    iter.fold(CriticalPaths::empty(), |acc, item| join(&acc, item))
}

pub fn join<Base: Clone + Ord>(
    left: &CriticalPaths<Base>,
    right: &CriticalPaths<Base>
) -> CriticalPaths<Base> {
    let mut new_facts = CriticalPaths::empty();
    for path in left.keys().chain(right.keys()) {
        let u = match (left.get(path), right.get(path)) {
            (Some(&CriticalUse::Value), _) => CriticalUse::Value,
            (_, Some(&CriticalUse::Value)) => CriticalUse::Value,
            (Some(&CriticalUse::Deref), _) => CriticalUse::Deref,
            (_, Some(&CriticalUse::Deref)) => CriticalUse::Deref,
            _ => unreachable!(),
        };
        // Insert is smart enough to remove duplicates & implications. Even the above isn't needed,
        // although it probably boosts performance.
        new_facts.insert(path.clone(), u);
    }
    new_facts
}


pub fn difference<Base: Clone + Debug + Ord>(
    left: &CriticalPaths<Base>,
    right: &BTreeSet<Path<Base>>
) -> CriticalPaths<Base> {
    let mut diff = left.clone();
    for path in right {
        diff.remove(&path, &CriticalUse::Value);
        diff.remove(&path, &CriticalUse::Deref);
    }
    diff
}

pub fn gen_by_statement<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                              lvalue: &Lvalue<'tcx>,
                                              rvalue: &Rvalue<'tcx>)
                                              -> CriticalPaths<BaseVar> {
    join(&gen_by_lvalue(info, lvalue), &gen_by_rvalue(info, rvalue))
}
pub fn gen_by_operand<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                            operand: &Operand<'tcx>)
                                            -> CriticalPaths<BaseVar> {
    use rustc::mir::repr::Operand::*;
    match operand {
        &Consume(ref lvalue) => gen_by_lvalue(info, lvalue),
        //Constants contain no projections - definitely safe.
        &Constant(_) => CriticalPaths::empty(),
    }
}

pub fn gen_by_lvalue<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                           lvalue: &Lvalue<'tcx>)
                                           -> CriticalPaths<BaseVar> {
    match lvalue {
        &Lvalue::Projection(box LvalueProjection { ref base, ref elem }) => {
            let mut facts = gen_by_lvalue(info, base);
            match elem {
                &ProjectionElem::Deref => {
                    if info.is_raw_ptr(base) {
                        facts.insert(lvalue_path(base), CriticalUse::Deref);
                    }
                },
                &ProjectionElem::Index(ref idx) => {
                    facts = join(&facts, &gen_by_operand(info, idx));
                    if let Some(path) = operand_path(idx) {
                        facts.insert(path, CriticalUse::Value);
                    }
                }
                _ => (),
            };
            facts
        },
        // Its just a basic variable.
        _ => CriticalPaths::empty(),
    }
}

pub fn gen_by_rvalue<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                           rvalue: &Rvalue<'tcx>)
                                           -> CriticalPaths<BaseVar> {
    use rustc::mir::repr::Rvalue::*;
    match *rvalue {
        Use(ref operand) |
        Repeat(ref operand, _) |
        Cast(_, ref operand, _) |
        UnaryOp(_, ref operand) => gen_by_operand(info, operand),

        BinaryOp(_, ref o1, ref o2) |
        CheckedBinaryOp(_, ref o1, ref o2) =>
            join(&gen_by_operand(info, o1), &gen_by_operand(info, o2)),

        Ref(_, _, ref lvalue) |
        Len(ref lvalue) => gen_by_lvalue(info, lvalue),

        Aggregate(_, ref operands) => {
            let generated = operands.iter().map(|o| gen_by_operand(info, o)).collect::<Vec<_>>();
            join_many(generated.iter())
        }

        InlineAsm { .. } => unimplemented!(),
        Box(_) => CriticalPaths::empty(),
    }
}

#[allow(unused_variables)]
pub fn kill<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                  lvalue: &Lvalue,
                                  rvalue: &Rvalue)
                                  -> BTreeSet<Path<BaseVar>> {
    BTreeSet::new()
}

/// Does a substitution from p1 to p2 in path. Returns a set of possible results from the
/// substitution. This is generic over the type of path, so it works for both TmpPath and Path
fn sub<'a, 'mir, 'gcx, 'tcx, T: Projectable>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                             path: Path<BaseVar>,
                                             p1: &Path<BaseVar>,
                                             p2: &T) -> Vec<T> {
//    path.sub_paths().filter_map(|(sub_path, extension)| {
//        if may_alias(info, sub_path, p1.as_ref()) {
//            let sub_path_copy = sub_path.clone();
//            sub_path_copy.extend_in_place(extension);
//            Some(sub_path_copy)
//        } else {
//            None
//        }
//    }).collect()
    let may_alias = info.may_alias(path.as_ref(), p1.as_ref());
    let mut inner_subs = match path.split() {
        (_, None) => vec![],
        (inner_path, Some(proj)) => {
            let mut paths = sub(info, inner_path, p1, p2);
            paths.iter_mut().map(|p| p.add_projection_in_place(proj.clone())).count();
            paths
        },
    };
    if may_alias {
        inner_subs.push(p2.clone());
    }
    inner_subs
}

/// Does a substitution from p1 to p2 in path. Returns a set of possible results from the
/// substitution.
///
/// The logic for this function is a follows: How might we affect the Value of `critical_path`?
/// Well either, we change the location the path locates or we change the value in the location.
///
/// First, we might change what location is located by `critical_path`, this is the same as when
/// dealing with Deref-sensitive paths.
///
/// Second, we might change the value in the location located by `critical_path`. This happens if
/// `critical_path` "may reach" the path we're writing into: `p1`, because if a location is
/// "value-sensitive" then so are all locations reachable from it.
fn val_sub<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                     critical_path: Path<BaseVar>,
                                     p1: &Path<BaseVar>,
                                     p2: &Path<BaseVar>) -> Vec<Path<BaseVar>> {
    if info.may_reach(critical_path.as_ref(), p1.as_ref()) || sub(info, critical_path, p1, p2).len() > 0 {
        vec![p2.clone()]
    } else { vec![] }
}

pub fn flow_assign_lval_lval<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                                   p1: &Path<BaseVar>,
                                                   l2: &Lvalue<'tcx>,
                                                   post_facts: &CriticalPaths<BaseVar>)
                                                   -> CriticalPaths<BaseVar> {
    let p2 = lvalue_path(l2);
    join_many(post_facts.iter().map(|(path, u)| {
        use self::CriticalUse::*;
        let facts = match u {
            &Deref => sub(info, path.clone(), p1, &p2),
            &Value => val_sub(info, path.clone(), p1, &p2),
        };
        facts.into_iter().map(|p| (p, u.clone())).collect()
    }).collect::<Vec<_>>().iter())
}

pub fn flow_assign_lval_ref_lval<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                                       p1: &Path<BaseVar>,
                                                       l2: &Lvalue<'tcx>,
                                                       post_facts: &CriticalPaths<BaseVar>)
                                                       -> CriticalPaths<BaseVar> {
    use self::CriticalUse::*;
    let p2 = lvalue_path(l2);
    let (value_post_facts, deref_post_facts): (Vec<_>,_)= post_facts.iter().partition(|&(_, u)| {
        match u {
            &Value => true,
            &Deref => false,
        }
    });
    let deref_pre_facts = join_many(deref_post_facts.iter().map(|&(path, _)| {
        let ref_p2 = TmpPath::from(p2.clone()).add_projection(TmpProjection::Ref);
        sub(info, path.clone(), p1, &ref_p2).into_iter().filter_map(|p| {
            reduce_and_secure(p, Deref)
        }).collect()
    }).collect::<Vec<_>>().iter());
    let value_pre_facts = flow_assign_lval_lval(info, p1, l2,
                                                &value_post_facts.into_iter()
                                                .map(|(a, b)| (a.clone(),b.clone()))
                                                .collect());
    join(&value_pre_facts, &deref_pre_facts)
}

/// This is the flow code for when making an assignment like:
///
/// ```
///     l1 = !l2
/// ```
///
/// Value-critical paths propegate as normal, however, deref-critical paths propegate differently.
/// Specifically, if any deref critical paths would propegate, then l2 becomes value critical
pub fn flow_assign_lval_op_lval<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                                      p1: &Path<BaseVar>,
                                                      l2: &Lvalue<'tcx>,
                                                      post_facts: &CriticalPaths<BaseVar>)
                                                      -> CriticalPaths<BaseVar> {
    use self::CriticalUse::*;
    let p2 = lvalue_path(l2);
    let (value_post_facts, deref_post_facts): (Vec<_>,_)= post_facts.iter().partition(|&(_, u)| {
        match u {
            &Value => true,
            &Deref => false,
        }
    });

    let l2_is_crit = deref_post_facts.iter().any(|&(p,_)| {
        p.as_ref().sub_paths().into_iter().any(|(sub_p,_)| info.may_alias(sub_p, p1.as_ref()))
    }) || value_post_facts.iter().any(|&(p,_)| val_sub(info, p.clone(), p1, &p2).len() > 0);

    let mut pre_facts = CriticalPaths::empty();
    if l2_is_crit { pre_facts.insert(p2, Value); }
    pre_facts
}

pub fn flow_assign_lval_operand<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                                      l_path: &Path<BaseVar>,
                                                      op: &Operand<'tcx>,
                                                      post_facts: &CriticalPaths<BaseVar>)
                                                      -> CriticalPaths<BaseVar> {
    use rustc::mir::repr::Operand::*;
    match op {
        &Consume(ref r_lval) => flow_assign_lval_lval(info, l_path, r_lval, post_facts),
        &Constant(_)         => CriticalPaths::empty(),
    }
}

pub fn flow_assign_lval_op_operand<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                                         l_path: &Path<BaseVar>,
                                                         op: &Operand<'tcx>,
                                                         post_facts: &CriticalPaths<BaseVar>)
                                                         -> CriticalPaths<BaseVar> {
    use rustc::mir::repr::Operand::*;
    match op {
        &Consume(ref r_lval) => flow_assign_lval_op_lval(info, l_path, r_lval, post_facts),
        &Constant(_)         => CriticalPaths::empty(),
    }
}

fn reduce_and_secure(p: TmpPath<BaseVar>, u: CriticalUse) -> Option<(Path<BaseVar>, CriticalUse)> {
    use path::TmpPath::*;
    use self::CriticalUse::*;
    let reduced = p.reduce_ref_deref();
    let secured = match (reduced, u) {
        (Proj(TmpProjection::Ref, _), Deref) => None,
        (Proj(TmpProjection::Ref, box inner), Value) => Some((inner, Value)),
        (p, u) => Some((p, u)),
    };
    secured.map(|(tmp_path, u)| (tmp_path.into_path(), u))
}

pub fn flow<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                  lvalue: &Lvalue<'tcx>,
                                  rvalue: &Rvalue<'tcx>,
                                  post_facts: &CriticalPaths<BaseVar>)
                                  -> CriticalPaths<BaseVar> {
    use rustc::mir::repr::Rvalue::*;
    use rustc::mir::repr::Operand::*;
    use rustc::mir::repr::AggregateKind::{Tuple, Adt, Closure, Vec as VecAgg};
    let p1 = &lvalue_path(lvalue);
    match rvalue {
        &Use(ref op) => flow_assign_lval_operand(info, p1, op, post_facts),
        &Repeat(ref op, _) => flow_assign_lval_operand(info, p1, op, post_facts),
        &Ref(_, _, ref l2) => flow_assign_lval_ref_lval(info, p1, l2, post_facts),
        &Len(ref l2) => flow_assign_lval_op_lval(info, p1, l2, post_facts),
        &Cast(_, Consume(ref l2), _) => {
            let mut pre_facts = flow_assign_lval_lval(info, p1, l2, post_facts);
            if info.is_ref(&l2) {
                pre_facts.remove(&lvalue_path(&l2),&CriticalUse::Deref);
            }
            pre_facts
        }
        &Cast(_, Constant(_), _) => CriticalPaths::empty(),
        &BinaryOp(_, ref op1, ref op2) |
        &CheckedBinaryOp(_, ref op1, ref op2) =>
            join(&flow_assign_lval_op_operand(info, p1, op1, post_facts),
                 &flow_assign_lval_op_operand(info, p1, op2, post_facts)),
        &UnaryOp(_, ref op) => flow_assign_lval_operand(info, p1, op, post_facts),
        &Box(_) => CriticalPaths::empty(),
        &Aggregate(VecAgg, ref operands) =>
            join_many(
                operands.iter()
                .map(|op| flow_assign_lval_operand(info, p1, op, post_facts))
                .collect::<Vec<_>>()
                .iter()
            ),
        &Aggregate(Tuple, ref operands) |
        &Aggregate(Closure(_, _), ref operands) =>
            join_many(
                operands.iter().enumerate()
                .map(|(field_idx, op)| {
                    let tuple_path = &p1.clone().tuple_field(field_idx);
                    flow_assign_lval_operand(info, tuple_path, op, post_facts)
                })
                .collect::<Vec<_>>()
                .iter()
            ),
        &Aggregate(Adt(_, variant_idx, _), ref operands) =>
            join_many(
                operands.iter().enumerate()
                .map(|(field_idx, op)| {
                    let adt_path = &p1.clone().adt_field(variant_idx, field_idx);
                    flow_assign_lval_operand(info, adt_path, op, post_facts)
                })
                .collect::<Vec<_>>()
                .iter()
            ),
        // TODO: Need a strategy for closures.
        // &Aggregate(Closure(_, _), ref ops) if ops.len() == 0 => CriticalPaths::empty(),
        // &Aggregate(Closure(_, _), _) => unimplemented!(),
        // &Aggregate(Closure(_, _), _) => CriticalPaths::empty(),
        &InlineAsm { .. } => unimplemented!(),
    }
}

pub fn transfer<'a, 'mir, 'gcx, 'tcx>(info: MIRInfo<'a, 'mir, 'gcx, 'tcx>,
                                      statement: &StatementKind<'tcx>,
                                      post_facts: &CriticalPaths<BaseVar>)
                                      -> CriticalPaths<BaseVar> {
    match statement {
        &StatementKind::Assign(ref lvalue, ref rvalue) => {
            let gen = &gen_by_statement(info, lvalue, rvalue);
            let kill = &kill(info, lvalue, rvalue);
            let flow = &flow(info, lvalue, rvalue, post_facts);
            join(&difference(&join(post_facts, flow), kill), gen)
        },
        _ => post_facts.clone(),
    }
}
