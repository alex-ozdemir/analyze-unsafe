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
};

use rustc_data_structures::indexed_vec::Idx;
use std::collections::{BTreeSet,BTreeMap};
use std::fmt::{self,Formatter};
use std::mem;

/// A trait for generalized paths: anything that you can add standard projections to (Derefs and
/// fields). This allows us to write code that works for both types of paths!
pub trait Projectable : Clone {
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

    fn tuple_field(mut self, field_idx: usize) -> Self {
        self.add_projection_in_place(Projection::Field(0, Some(field_idx)));
        self
    }

    fn adt_field(mut self, variant_idx: usize, field_idx: usize) -> Self {
        self.add_projection_in_place(Projection::Field(variant_idx, Some(field_idx)));
        self
    }
}

#[derive(Hash,PartialEq,Eq,PartialOrd,Ord,Clone)]
pub struct Path {
    projections: Vec<Projection>,
    base: BaseVar,
}

pub struct PathRef<'a> {
    projections: &'a [Projection],
    base: &'a BaseVar
}

//TODO: Rewrite with slice pattterns <3
#[derive(Clone)]
pub enum TmpProjection {
    Proj(Projection),
    Ref,
}

#[derive(Clone)]
pub enum TmpPath {
    Base(BaseVar),
    Proj(TmpProjection, Box<TmpPath>),
}

impl From<Path> for TmpPath {
    fn from(from: Path) -> Self {
        match from.split() {
            (inner, None) => TmpPath::Base(inner.base),
            (inner, Some(proj)) =>
                TmpPath::Proj(TmpProjection::Proj(proj), box TmpPath::from(inner)),
        }
    }
}

impl Projectable for TmpPath {
    fn add_projection_in_place(&mut self, proj: Projection) {
        let tmp_self = mem::replace(self, TmpPath::Base(BaseVar::Temp(Temp::new(0))));
        *self = TmpPath::Proj(TmpProjection::Proj(proj), box tmp_self);
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

impl TmpPath {
    pub fn add_projection(self, tmp_proj: TmpProjection) -> Self {
        TmpPath::Proj(tmp_proj, box self)
    }

    fn from_base_var(base: BaseVar) -> Self {
        TmpPath::Base(base)
    }

    pub fn into_path(self) -> Path {
        use self::TmpPath::*;
        match self {
            Proj(TmpProjection::Ref, _) => bug!("Found a ref when converting TmpPath to Path"),
            Proj(TmpProjection::Proj(proj), box inner) => inner.into_path().add_projection(proj),
            Base(var) => Path::from_base_var(var),
        }
    }

    pub fn reduce_ref_deref(self) -> Self {
        use self::TmpPath::*;
        match self {
            Base(var) => TmpPath::from_base_var(var),
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

impl Projectable for Path {
    fn add_projection_in_place(&mut self, p: Projection) {
        self.projections.push(p);
    }

    fn last_projection_mut(&mut self) -> Option<&mut Projection> {
        self.projections.last_mut()
    }
}

impl Path {

    pub fn new(base: BaseVar, projs: Vec<Projection>) -> Path {
        Path {projections: projs, base: base}
    }

    pub fn from_base_var(base: BaseVar) -> Path {
        Path { projections: vec![], base: base }
    }

    pub fn add_projection(mut self, p: Projection) -> Path {
        self.projections.push(p);
        self
    }

    pub fn as_ref(&self) -> PathRef {
        PathRef{ projections: self.projections.as_slice(), base: &self.base }
    }

    /// Split the Path into a PathRef and Extension at `idx`.
    ///
    /// ## Panics
    ///
    /// If `idx` is greater than or equal to the number of projections
    fn split_at(&self, idx: usize) -> (PathRef, &[Projection]) {
        let (head, tail) = self.projections.as_slice().split_at(idx);
        let path_ref = PathRef{ projections: head, base: &self.base };
        (path_ref, tail)
    }

    pub fn extend_in_place(&mut self, extension: &[Projection]) {
        self.projections.extend_from_slice(extension);
    }

    pub fn sub_paths(&self) -> Vec<(PathRef,&[Projection])> {
        (0..self.projections.len()).map(|i| self.split_at(i)).collect()
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

    pub fn split(mut self) -> (Self, Option<Projection>) {
        let proj = self.projections.pop();
        (self, proj)
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for projection in self.projections.iter() {
            match *projection {
                Projection::Deref => try!(write!(f, "*(")),
                Projection::Field(_, _) => try!(write!(f, "(")),
            }
        }
        try!(write!(f, "{:?}", self.base));
        for projection in self.projections.iter().rev() {
            match *projection {
                Projection::Deref => try!(write!(f, ")")),
                Projection::Field(idx1, idx2) => try!(write!(f, ".{}#{})", idx1, idx2.unwrap())),
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

