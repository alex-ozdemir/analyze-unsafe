// Alex Ozdemir <aozdemir@hmc.edu>
// Library for analyzing unsafe code in rust as a compiler plugin

use rustc::hir;
use rustc::hir::{intravisit,Unsafety};
use rustc::session::Session;
use rustc::ty;
use syntax::{abi,ast};

use syntax::codemap::{CodeMap,ExpnInfo,ExpnFormat,Span};

use std::mem;

#[allow(unused_imports)]
use std::io::Write;

const snippet_length: usize = 40;

macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

#[derive(Clone, PartialEq, Eq, Debug, RustcEncodable, RustcDecodable)]
pub struct Indexed<T> {
    index: u64,
    span: String,
    snippet: String,
    macro_origin: MacroOrigin,
    item: T,
}

impl<T> Indexed<T> {
    /// Create a new indexed item with
    ///     `index` - its statement number in the enclosing block
    ///     `span` - span of the item
    ///     `codemap` - used to interpret the span
    ///     `snippet` - whether or not to include a code snippet
    ///     `macro_origin` - whether this item originated in a macro
    pub fn new(index: u64,
               item: T,
               span: Span,
               codemap: &CodeMap,
               snippet: bool,
               macro_origin: MacroOrigin) -> Indexed<T> {
        let mut span_string = codemap.span_to_string(span);
        let mut snippet = if snippet {
            codemap.span_to_snippet(span).unwrap_or_else(|_| String::new())
        } else { "".to_string() };
        if snippet.len() > snippet_length {
            while snippet.len() > snippet_length - 1 {
                snippet.pop();
            }
            snippet.push('@');
        }
        Indexed {
            index: index,
            span: span_string,
            snippet: snippet,
            macro_origin: macro_origin,
            item: item,
        }
    }
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
    name: String,
}

impl FnDecl {
    pub fn new(block: Box<Block>, unsafety: Unsafety, name: String) -> Self {
        FnDecl { unsaf: is_unsafe(unsafety), block: block, name: name }
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
pub enum MacroOrigin {
    NotMacro, LocalMacro, ExternalMacro,
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

pub struct UnsafeSummarizer<'a, 'tcx: 'a,'ast> {
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    index: u64,
    session: &'ast Session,
    unsafe_points: Vec<Indexed<UnsafePoint>>,
    stack: Vec<(u64, Vec<Indexed<UnsafePoint>>)>,
    pub functions: Vec<FnDecl>,
}

impl<'a,'tcx:'a,'ast> UnsafeSummarizer<'a,'tcx,'ast> {
    pub fn new(tcx: ty::TyCtxt<'a,'tcx,'tcx>, session: &'ast Session) -> UnsafeSummarizer<'a,'tcx,'ast> {
        UnsafeSummarizer {
            tcx: tcx,
            session: session,
            index: 0,
            unsafe_points: vec![],
            stack: vec![],
            functions: vec![],
        }
    }
    /// Create a new indexed item with
    ///     `index` - its statement number in the enclosing block
    ///     `span` - span of the item
    ///     `snippet` - whether or not to include a code snippet
    pub fn mk_indexed<T>(&self, index: u64, item: T, span: Span, snippet: bool) -> Indexed<T> {
        let macro_origin = self.get_macro_origin(span);
        Indexed::new(index, item, span, self.session.codemap(), snippet, macro_origin)
    }

    /// Returns true if this `expn_info` was expanded by any macro.
    /// This function taken from `clippy`
    fn in_macro(&self, span: Span) -> bool {
        self.session.codemap().with_expn_info(span.expn_id, |info| info.is_some())
    }

    /// Returns true if the macro that expanded the crate was outside of the current crate or was a
    /// compiler plugin.
    /// This function taken from `clippy`
    fn in_external_macro(&self, span: Span) -> bool {
        /// Invokes `in_macro` with the expansion info of the given span slightly heavy, try to use
        /// this after other checks have already happened.
        fn in_macro_ext(codemap: &CodeMap, opt_info: Option<&ExpnInfo>) -> bool {
            // no ExpnInfo = no macro
            opt_info.map_or(false, |info| {
                if let ExpnFormat::MacroAttribute(..) = info.callee.format {
                    // these are all plugins
                    return true;
                }
                // no span for the callee = external macro
                info.callee.span.map_or(true, |span| {
                    // no snippet = external macro or compiler-builtin expansion
                    codemap.span_to_snippet(span).ok()
                        .map_or(true, |code| !code.starts_with("macro_rules"))
                })
            })
        }
        let codemap = self.session.codemap();
        codemap.with_expn_info(span.expn_id, |info| in_macro_ext(codemap, info))
    }

    fn get_macro_origin(&self, span: Span) -> MacroOrigin {
        if self.in_macro(span) {
            if self.in_external_macro(span) { MacroOrigin::ExternalMacro }
            else { MacroOrigin::LocalMacro }
        } else { MacroOrigin::NotMacro }
    }
}

impl<'a, 'tcx: 'a, 'ast> UnsafeSummarizer<'a, 'tcx, 'ast> {
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
        let indexed_pt = self.mk_indexed(self.index, block, b.span, false);
        self.unsafe_points.push(indexed_pt);
    }
    fn visit_fn_post<'v>(&mut self,
                         fk: intravisit::FnKind<'v>,
                         _: &'v hir::FnDecl,
                         _: &'v hir::Block,
                         span: Span,
                         id: ast::NodeId) {
        use ::rustc::hir::intravisit::FnKind::{ItemFn,Method,Closure};
        let Indexed{ item, .. } = self.unsafe_points.pop().unwrap();
        if let UnsafePoint::Block(boxed_block) = item {
            let (index, unsafe_points) = self.stack.pop().unwrap();
            self.index = index;
            self.unsafe_points = unsafe_points;
            match fk {
                ItemFn(_, _, unsafety, _, _, _, _) |
                Method(_, &hir::MethodSig { unsafety, .. }, _, _) => {
                    let name = self.tcx.node_path_str(id);
                    self.functions.push(FnDecl::new(boxed_block, unsafety, name));
                }
                Closure(_) => {
                    let closure = UnsafePoint::Closure(boxed_block);
                    let indexed_pt = self.mk_indexed(self.index, closure, span, false);
                    self.unsafe_points.push(indexed_pt);
                }
            };
        } else {
            panic!("Found something other than a block under a fn: {:?}", item);
        }
    }
}

impl<'a, 'tcx: 'a, 'ast, 'v> intravisit::Visitor<'v> for UnsafeSummarizer<'a, 'tcx, 'ast> {

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
                let fn_ty = self.tcx.expr_ty_adjusted(fn_expr);
                let fn_safety = get_fn_safety(fn_ty);
                let fn_ffi = get_fn_ffi(fn_ty);
//                if self.in_closure && fn_safety.unsaf.clone() {
//                    self.session.span_warn(expr.span, "Unsafe Call in closure");
//                }
                let unsafe_call = UnsafePoint::Call(fn_safety,fn_ffi);
                let indexed_pt = self.mk_indexed(self.index, unsafe_call, expr.span, true);
                self.unsafe_points.push(indexed_pt);
            },
            hir::Expr_::ExprMethodCall(_, _, _) => {
                let method_call = ty::MethodCall::expr(expr.id);
                let fn_ty = self.tcx.tables.borrow().method_map[&method_call].ty;
                let fn_safety = get_fn_safety(fn_ty);
                let fn_ffi = get_fn_ffi(fn_ty);
//                if self.in_closure && fn_safety.unsaf.clone() {
//                    self.session.span_warn(expr.span, "Unsafe Call in closure");
//                }
                let unsafe_call = UnsafePoint::Call(fn_safety,fn_ffi);
                let indexed_pt = self.mk_indexed(self.index, unsafe_call, expr.span, true);
                self.unsafe_points.push(indexed_pt);
            },
            hir::Expr_::ExprUnary(hir::UnOp::UnDeref, ref sub_expr) => {
                let tys = self.tcx.node_id_to_type(sub_expr.id);
                if let ty::TyRawPtr(_) = tys.sty {
                    let indexed_pt =
                        self.mk_indexed(self.index, UnsafePoint::Deref, expr.span, true);
                    self.unsafe_points.push(indexed_pt);
                    let in_macro = self.session.codemap().with_expn_info(expr.span.expn_id, |i| i.is_some());
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

fn get_fn_safety(ty: ty::Ty) -> Unsafe {
    match ty.sty {
        ty::TyFnDef(_, _, ref f) |
        ty::TyFnPtr(ref f) => Unsafe::new(f.unsafety),
        _ => Unsafe { unsaf: false },
    }
}

fn get_fn_ffi(ty: ty::Ty) -> FFI {
    match ty.sty {
        ty::TyFnDef(_, _, ref f) |
        ty::TyFnPtr(ref f) => FFI::new(f.abi),
        _ => FFI { is_ffi: false },
    }
}
