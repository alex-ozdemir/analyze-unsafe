#![allow(dead_code,unused_imports)]
use base_var::BaseVar;

use rustc::mir::repr::{CastKind,
                       Constant,
                       Lvalue,
                       LvalueProjection,
                       Operand,
                       ProjectionElem,
                       Mir,
                       Rvalue,
                       Statement,
                       StatementKind,
                       Temp,
};

use rustc::ty::{TypeVariants,
                TypeAndMut,
                AdtDefData,
                TyCtxt,
                Ty,
};

use rustc::hir::def_id::DefId;
use syntax::ast::NodeId;

use rustc_data_structures::indexed_vec::Idx;
use std::collections::{BTreeSet,BTreeMap};
use std::fmt::{self,Formatter,Debug};
use std::{mem, ptr};

/// A trait for generalized paths: anything that you can add standard projections to (Derefs and
/// fields). This allows us to write code that works for both types of paths!
pub trait Projectable : Clone + Debug {
    fn add_projection_in_place(&mut self, p: Projection);

    fn last_projection_mut(&mut self) -> Option<&mut Projection>;

    fn downcast_in_place(&mut self, variant_idx: usize) {
        self.add_projection_in_place(Projection::Field(variant_idx, None))
    }

    fn field_in_place(&mut self, field_idx: usize) {
        let done = self.last_projection_mut().map(|proj| {
            let mut done = false;
            let temp = mem::replace(proj, Projection::Deref);
            *proj = match temp {
                Projection::Field(i, None) => {
                    done = true;
                    Projection::Field(i, Some(field_idx.index()))
                },
                x => x,
            };
            done
        }).unwrap_or(false);
        if !done {
            self.add_projection_in_place(Projection::Field(0, Some(field_idx.index())))
        }
    }

    fn tuple_field_in_place(&mut self, field_idx: usize) {
        self.add_projection_in_place(Projection::Field(0, Some(field_idx)));
    }

    fn deref_in_place(&mut self) {
        self.add_projection_in_place(Projection::Deref);
    }

    fn tuple_field(mut self, field_idx: usize) -> Self {
        self.tuple_field_in_place(field_idx);
        self
    }

    fn adt_field(mut self, variant_idx: usize, field_idx: usize) -> Self {
        self.add_projection_in_place(Projection::Field(variant_idx, Some(field_idx)));
        self
    }
}

#[derive(Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub struct Path<Base> {
    projections: Vec<Projection>,
    base: Base,
}

#[derive(Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub struct PathRef<'a, Base: 'a> {
    pub projections: &'a [Projection],
    pub base: &'a Base,
}

//TODO: Rewrite with slice pattterns <3
#[derive(Clone,Debug)]
pub enum TmpProjection {
    Proj(Projection),
    Ref,
}

#[derive(Clone,Debug)]
pub enum TmpPath<Base> {
    Base(Base),
    Proj(TmpProjection, Box<TmpPath<Base>>),
}

impl<Base: Clone + Eq> From<Path<Base>> for TmpPath<Base> {
    fn from(from: Path<Base>) -> Self {
        match from.split() {
            (inner, None) => TmpPath::Base(inner.base),
            (inner, Some(proj)) =>
                TmpPath::Proj(TmpProjection::Proj(proj), box TmpPath::from(inner)),
        }
    }
}

impl<Base: Clone + Debug> Projectable for TmpPath<Base> {
    fn add_projection_in_place(&mut self, proj: Projection) {
        // TODO: Eliminate copy
        *self = TmpPath::Proj(TmpProjection::Proj(proj), box self.clone())
    }

    fn last_projection_mut(&mut self) -> Option<&mut Projection> {
        match self {
            &mut TmpPath::Proj(ref mut proj, _) => {
                match proj {
                    &mut TmpProjection::Ref => None,
                    &mut TmpProjection::Proj(ref mut proj) => Some(proj),
                }
            },
            &mut TmpPath::Base(_) => None,
        }
    }
}

impl<Base: Clone + Eq> TmpPath<Base> {
    pub fn add_projection(self, tmp_proj: TmpProjection) -> Self {
        TmpPath::Proj(tmp_proj, box self)
    }

    fn from_base(base: Base) -> Self {
        TmpPath::Base(base)
    }

    pub fn into_path(self) -> Path<Base> {
        use self::TmpPath::*;
        match self {
            Proj(TmpProjection::Ref, _) => bug!("Found a ref when converting TmpPath to Path"),
            Proj(TmpProjection::Proj(proj), box inner) => inner.into_path().add_projection(proj),
            Base(var) => Path::from_base(var),
        }
    }

    pub fn reduce_ref_deref(self) -> Self {
        use self::TmpPath::*;
        match self {
            Base(var) => TmpPath::from_base(var),
            Proj(TmpProjection::Proj(Projection::Deref), box Proj(TmpProjection::Ref, box inner))
                => inner.reduce_ref_deref(),
            Proj(TmpProjection::Proj(Projection::Field(_,_)), box Proj(TmpProjection::Ref, _))
                => bug!("Found a path which read the field of a ref! Type System violation?"),
            Proj(TmpProjection::Ref, box Proj(TmpProjection::Ref, _))
                => bug!("Found a path which ref'd a ref! Bug in Sub?"),
            Proj(proj, box inner) => inner.reduce_ref_deref().add_projection(proj),
        }
    }
}

impl<Base: Clone + Debug> Projectable for Path<Base> {
    fn add_projection_in_place(&mut self, p: Projection) {
        self.projections.push(p);
    }

    fn last_projection_mut(&mut self) -> Option<&mut Projection> {
        self.projections.last_mut()
    }
}

impl<'a, Base> PathRef<'a, Base> {
    pub fn has_indirection(&self) -> bool {
        self.projections.iter().any(|p| p == &Projection::Deref)
    }
}

impl<Base: Clone> Path<Base> {
    pub fn as_ref(&self) -> PathRef<Base> {
        PathRef{ projections: self.projections.as_slice(), base: &self.base }
    }
}

impl<Base: Clone + Eq> Path<Base> {

    pub fn new(base: Base, projs: Vec<Projection>) -> Path<Base> {
        Path {projections: projs, base: base}
    }

    /// Cut the path down to at most `len` projections. Reports `true` if projections were actually
    /// cut off.
    pub fn truncate(&mut self, len: usize) -> bool {
        let needs_truncation = self.projections.len() > len;
        self.projections.truncate(len);
        needs_truncation
    }

    pub fn pop_last(&mut self) -> Option<Projection> {
        self.projections.pop()
    }

    pub fn change_base(&mut self, base: Base) {
        self.base = base;
    }

    pub fn replace_base(&mut self, base: &Base, path: Path<Base>) {
        if self.base == *base {
            let old_self = mem::replace(self, path);
            self.extend_in_place(old_self.as_extension());
        }
    }

    pub fn as_extension(&self) -> &[Projection] {
        self.projections.as_slice()
    }

    pub fn from_base(base: Base) -> Path<Base> {
        Path { projections: vec![], base: base }
    }

    pub fn add_projection(mut self, p: Projection) -> Path<Base> {
        self.projections.push(p);
        self
    }

    /// Split the Path into a PathRef and Extension at `idx`.
    ///
    /// ## Panics
    ///
    /// If `idx` is greater than or equal to the number of projections
    fn split_at(&self, idx: usize) -> (PathRef<Base>, &[Projection]) {
        let (head, tail) = self.projections.as_slice().split_at(idx);
        let path_ref = PathRef{ projections: head, base: &self.base };
        (path_ref, tail)
    }

    pub fn extend_in_place(&mut self, extension: &[Projection]) {
        self.projections.extend_from_slice(extension);
    }

    pub fn sub_paths(&self) -> Vec<(PathRef<Base>,&[Projection])> {
        (0..self.projections.len()).map(|i| self.split_at(i)).collect()
    }

    pub fn strip_highest_deref(mut self) -> Option<Path<Base>> {
        let index = self.projections.iter().rposition(|proj| proj.is_deref());
        index.map(|index| {
            self.projections.remove(index);
            self
        })
    }

    pub fn sub(&self, from: &Path<Base>, to: &Path<Base>) -> Option<Path<Base>> {
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

    pub fn contains(&self, other: &Path<Base>) -> bool {
        (self.base == other.base) && self.projections.starts_with(other.projections.as_slice())
    }

    pub fn sub_if_possible(self, from: &Path<Base>, to: &Path<Base>) -> Path<Base> {
        self.sub(from, to).unwrap_or(self)
    }

    pub fn split(mut self) -> (Self, Option<Projection>) {
        let proj = self.projections.pop();
        (self, proj)
    }

    pub fn has_base(&self, base: &Base) -> bool {
        self.base == *base
    }

    pub fn base(&self) -> &Base {
        &self.base
    }
}

impl Path<BaseVar> {
    pub fn of_argument(&self) -> bool {
        match self.base {
            BaseVar::Arg(_) => true,
            _ => false,
        }
    }
    pub fn of_return(&self) -> bool {
        match self.base {
            BaseVar::ReturnPointer => true,
            _ => false,
        }
    }
    pub fn may_escape(&self) -> bool {
        self.of_return() || (self.of_argument() && self.as_ref().has_indirection())
    }
}

impl<'a,Base: Debug> Debug for PathRef<'a,Base> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for projection in self.projections.iter().rev() {
            match *projection {
                Projection::Deref => try!(write!(f, "(*")),
                Projection::Field(_, _) => try!(write!(f, "(")),
            }
        }
        try!(write!(f, "{:?}", self.base));
        for projection in self.projections.iter() {
            match *projection {
                Projection::Deref => try!(write!(f, ")")),
                Projection::Field(idx1, idx2) => try!(write!(f, ".{}#{})", idx1, idx2.unwrap())),
            }
        }
        write!(f, "")
    }
}

impl<Base: Clone + Debug> Debug for Path<Base> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self.as_ref())
    }
}

#[derive(Debug,Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub enum Projection {
    Deref,
    Field(usize,Option<usize>),
}

impl Projection {
    pub fn is_deref(&self) -> bool {
        match *self {
            Projection::Deref => true,
            Projection::Field(_, _) => false
        }
    }
}

pub fn paths_to_field_acc<'tcx:'mir,'mir,Base: Clone + Eq + Debug>(
    current: &mut Path<Base>,
    ty: Ty<'tcx>,
    field_did: DefId,
    tcx: TyCtxt<'mir,'tcx,'tcx>
) -> Vec<Path<Base>> {

    use rustc::ty::TypeVariants::*;
    match ty.sty {
        TyBool | TyChar | TyInt(_) | TyUint(_) | TyFloat(_) |
        TyStr | TyInfer(_) | TyParam(_) | TyError => vec![],
        TyArray(ty, _) | TySlice(ty) => {
            paths_to_field_acc(current, ty, field_did, tcx)
        }
        TyBox(inner_ty) |
        TyRawPtr(TypeAndMut{ ty: inner_ty, .. }) |
        TyRef(_, TypeAndMut{ ty: inner_ty, .. }) => {
            current.deref_in_place();
            let out = paths_to_field_acc(current, inner_ty, field_did, tcx);
            current.pop_last();
            out
        }
        TyEnum(adt_def, substs) |
        TyStruct(adt_def, substs) => {
            let mut paths = vec![];
            for var_idx in 0..(adt_def.variants.len()) {
                for field_idx in 0..(adt_def.variants[var_idx].fields.len()) {
                    let field_proj = Projection::Field(var_idx, Some(field_idx));
                    let ref field = adt_def.variants[var_idx].fields[field_idx];
                    current.add_projection_in_place(field_proj);
                    if field.did == field_did {
                        paths.push(current.clone())
                    }
                    let t = field.ty(tcx, substs);
                    paths.extend(paths_to_field_acc(current, t, field_did, tcx));
                    current.pop_last();
                }
            }
            paths
        }
        TyTuple(ref ts) => {
            let mut paths = vec![];
            for idx in 0..(ts.len()) {
                let ty = ts[idx];
                current.tuple_field_in_place(idx);
                paths.extend(paths_to_field_acc(current, ty, field_did, tcx));
                current.pop_last();
            }
            paths
        }
        TyClosure(_, _) | TyProjection(_) | TyTrait(_) | TyFnDef(_, _, _) | TyFnPtr(_) => vec![],
    }
}

