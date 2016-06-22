// Alex Ozdemir <aozdemir@hmc.edu>
// Library for analyzing unsafe code in rust as a compiler plugin

use ::rustc::hir;
use ::rustc::hir::{intravisit,Unsafety};
use ::rustc::ty;
use ::syntax::{abi,ast};

use ::syntax::codemap::Span;

use std::mem;

#[allow(unused_imports)]
use std::io::Write;

macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

#[derive(Clone, PartialEq, Eq, Debug, RustcEncodable, RustcDecodable)]
pub struct Indexed<T> {
    index: u64,
    item: T,
}

impl<T> Indexed<T> {
    pub fn new(index: u64, item: T) -> Indexed<T> { Indexed { index: index, item: item } }
}

#[derive(Clone, PartialEq, Eq, Debug, RustcEncodable, RustcDecodable)]
pub struct Block {
    size: u64,
    unsaf: bool,
    unsafe_points: Vec<Indexed<UnsafePoint>>,
}
impl Block {
    pub fn new(unsafety: Unsafety, size: u64, unsafe_points: Vec<Indexed<UnsafePoint>>) -> Block {
        Block { unsaf: is_unsafe(unsafety), size: size, unsafe_points: unsafe_points }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, RustcEncodable, RustcDecodable)]
pub struct FnDecl {
    block: Box<Block>,
    unsaf: bool,
}

impl FnDecl {
    pub fn new(block: Box<Block>, unsafety: Unsafety) -> Self {
        FnDecl { unsaf: is_unsafe(unsafety), block: block }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, RustcEncodable, RustcDecodable)]
pub struct FFI {
    is_ffi: bool,
}

impl FFI {
    pub fn new(h: abi::Abi) -> FFI {
        FFI { is_ffi: match h {
            abi::Abi::C | abi::Abi::System => true,
            _ => false,
        } }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, RustcEncodable, RustcDecodable)]
pub struct Unsafe {
    unsaf: bool,
}

impl Unsafe {
    pub fn new(h: Unsafety) -> Unsafe {
        Unsafe { unsaf: is_unsafe(h) }
    }
}

fn is_unsafe(h: Unsafety) -> bool {
    match h {
        Unsafety::Normal => false,
        Unsafety::Unsafe => true,
    }
}

#[derive(Clone, PartialEq, Eq, Debug, RustcEncodable, RustcDecodable)]
pub enum UnsafePoint {
    Deref,
    Call(Unsafe,FFI),
    Closure(Box<Block>),
    Block(Box<Block>),
}

pub struct UnsafeSummarizer<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    index: u64,
    unsafe_points: Vec<Indexed<UnsafePoint>>,
    stack: Vec<(u64, Vec<Indexed<UnsafePoint>>)>,
    pub functions: Vec<FnDecl>,
}

impl<'a,'tcx:'a> UnsafeSummarizer<'a,'tcx> {
    pub fn new(tcx: ty::TyCtxt<'a,'tcx,'tcx>) -> UnsafeSummarizer<'a,'tcx> {
        UnsafeSummarizer {
            tcx: tcx,
            index: 0,
            unsafe_points: vec![],
            stack: vec![],
            functions: vec![],
        }
    }
}

impl<'a, 'tcx: 'a> UnsafeSummarizer<'a, 'tcx> {
    fn visit_block_post<'v>(&mut self, b: &'v hir::Block) {
        use ::rustc::hir::BlockCheckMode::*;
        use ::rustc::hir::UnsafeSource::UserProvided;
        if b.expr.is_some() { self.index += 1 }
        let unsafety = match *b {
            hir::Block{rules: DefaultBlock, ..} => Unsafety::Normal,
            hir::Block{rules: UnsafeBlock(UserProvided), ..} |
            hir::Block{rules: PushUnsafeBlock(UserProvided), ..} |
            hir::Block{rules: PopUnsafeBlock(UserProvided), ..} => Unsafety::Unsafe,
            _ => Unsafety::Normal,
        };
        let (index, mut unsafe_points) = self.stack.pop().unwrap();
        mem::swap(&mut unsafe_points, &mut self.unsafe_points);
        let block = UnsafePoint::Block(
            Box::new(Block::new(unsafety, self.index, unsafe_points))
        );
        self.index = index;
        self.unsafe_points.push(Indexed::new(self.index, block));
    }
    fn visit_fn_post<'v>(&mut self,
                         fk: intravisit::FnKind<'v>,
                         _: &'v hir::FnDecl,
                         _: &'v hir::Block,
                         _: Span,
                         _: ast::NodeId) {
        use ::rustc::hir::intravisit::FnKind::{ItemFn,Method,Closure};
        let Indexed{ item, .. } = self.unsafe_points.pop().unwrap();
        if let UnsafePoint::Block(boxed_block) = item {
            let (index, unsafe_points) = self.stack.pop().unwrap();
            self.index = index;
            self.unsafe_points = unsafe_points;
            match fk {
                ItemFn(_, _, unsafety, _, _, _, _) |
                Method(_, &hir::MethodSig { unsafety, .. }, _, _) => {
                    self.functions.push(FnDecl::new(boxed_block, unsafety));
                }
                Closure(_) => {
                    let closure = UnsafePoint::Closure(boxed_block);
                    self.unsafe_points.push(Indexed::new(self.index, closure));
                }
            };
        } else {
            panic!("Found something other than a block under a fn: {:?}", item);
        }
    }
}

impl<'a, 'tcx: 'a, 'v> intravisit::Visitor<'v> for UnsafeSummarizer<'a, 'tcx> {

    fn visit_block(&mut self, b: &'v hir::Block) {
        self.stack.push( (self.index, mem::replace(&mut self.unsafe_points, vec![])) );
        self.index = 0;
        intravisit::walk_block(self, b);
        self.visit_block_post(b);
    }
    fn visit_stmt(&mut self, s: &'v hir::Stmt) {
        intravisit::walk_stmt(self, s);
        self.index += 1;
    }
    fn visit_expr(&mut self, expr: &'v hir::Expr) {
        match expr.node {
            hir::Expr_::ExprCall(ref fn_expr, _) => {
                let tys = self.tcx.node_id_to_type(fn_expr.id);
                if let ty::TyFnDef(_, _,
                                   &ty::BareFnTy{unsafety, abi, ..}) = tys.sty {
                    self.unsafe_points.push(
                        Indexed::new(self.index,
                                     UnsafePoint::Call(Unsafe::new(unsafety),FFI::new(abi)))
                    );
                }
            },
            hir::Expr_::ExprUnary(hir::UnOp::UnDeref, ref sub_expr) => {
                let tys = self.tcx.node_id_to_type(sub_expr.id);
                if let ty::TyRawPtr(_) = tys.sty {
                    self.unsafe_points.push(Indexed::new(self.index, UnsafePoint::Deref));
                }
            },
            _ => { /* No other unsafe operations */ },
        }
        intravisit::walk_expr(self, expr);
    }
    fn visit_fn(&mut self,
                fk: intravisit::FnKind<'v>,
                fd: &'v hir::FnDecl,
                b: &'v hir::Block,
                s: Span,
                id: ast::NodeId) {
        self.stack.push( (self.index, mem::replace(&mut self.unsafe_points, vec![])) );
        self.index = 0;
        self.visit_block(b);
        self.visit_fn_post(fk, fd, b, s, id);
    }
}

