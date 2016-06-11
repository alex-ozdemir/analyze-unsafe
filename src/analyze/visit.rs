// Alex Ozdemir <aozdemir@hmc.edu>
// Library for analyzing unsafe code in rust as a compiler plugin

//extern crate rustc;
//extern crate syntax;

use ::rustc::hir;
use ::rustc::hir::{intravisit,HirVec,Unsafety};
//use ::rustc::hir::intravisit::Visit;
use ::rustc::ty;
use ::syntax::{abi,ast};

use ::syntax::codemap::Span;
use ::syntax::ptr::P;

pub trait VisitUnsafe<'a, 'tcx: 'a, 'b, 'v> : intravisit::Visitor<'v> {
    // Gets the Type Context
    fn get_tcx(&self) -> ty::TyCtxt<'a, 'tcx, 'tcx>;
    fn get_krate(&self) -> &'b hir::Crate;
    fn visit_unsafe_block(&mut self,
                          stmts: &HirVec<hir::Stmt>,
                          expr: &Option<P<hir::Expr>>,
                          id: ast::NodeId,
                          span: Span) {
    }
    fn visit_unsafe_block_post(&mut self,
                               stmts: &HirVec<hir::Stmt>,
                               expr: &Option<P<hir::Expr>>,
                               id: ast::NodeId,
                               span: Span) {
    }
    fn visit_unsafe_fn_call(&mut self,
                            fn_expr: &'v P<hir::Expr>,
                            args_expr: &'v HirVec<P<hir::Expr>>) {
    }
    fn visit_unsafe_impl(&mut self,
                         polarity: &'v hir::ImplPolarity,
                         generics: &'v hir::Generics,
                         trait_ref: &'v Option<hir::TraitRef>,
                         self_ty: &'v P<hir::Ty>,
                         items: &'v HirVec<hir::ImplItem>) {
    }
    fn visit_foreign_mod(&mut self, module: &'v hir::ForeignMod) {
    }
    fn visit_closure(&mut self,
                     fn_decl: &'v hir::FnDecl,
                     block: &'v hir::Block,
                     span: Span,
                     attrs: &'v [ast::Attribute],
                     _: ast::NodeId) {
    }
    fn visit_closure_post(&mut self,
                          fn_decl: &'v hir::FnDecl,
                          block: &'v hir::Block,
                          span: Span,
                          attrs: &'v [ast::Attribute],
                          _: ast::NodeId) {
    }
    fn visit_unsafe_fn(&mut self,
                       fn_info: FnMethodInfo<'v>,
                       vis: &'v hir::Visibility) {
    }
    fn visit_unsafe_fn_post(&mut self,
                            fn_info: FnMethodInfo<'v>,
                            vis: &'v hir::Visibility) {
    }
    fn visit_unsafe_method(&mut self,
                           method_info: FnMethodInfo<'v>,
                           vis: Option<&'v hir::Visibility>) {
    }
    fn visit_unsafe_method_post(&mut self,
                                method_info: FnMethodInfo<'v>,
                                vis: Option<&'v hir::Visibility>) {
    }
    fn visit_expr(&mut self, expr: &'v hir::Expr) {
        if let hir::Expr_::ExprCall(ref fn_expr, ref args_expr) = expr.node {
            let tys = self.get_tcx().node_id_to_type(fn_expr.id);
            if let ty::TyFnDef(_, _,
                               &ty::BareFnTy{unsafety: Unsafety::Unsafe, abi, ..}) = tys.sty {
                self.visit_unsafe_fn_call(fn_expr, args_expr);
            };
        };
        intravisit::walk_expr(self, expr);
    }
    fn visit_block(&mut self, b: &'v hir::Block) {
        use rustc::hir::BlockCheckMode::UnsafeBlock;
        use rustc::hir::UnsafeSource::UserProvided;
        match *b {
            hir::Block{rules: UnsafeBlock(UserProvided), ref stmts, ref expr, ref id, ref span} =>
                self.visit_unsafe_block(stmts, expr, *id, *span),
            _ => { },
        };

        intravisit::walk_block(self, b);

        match *b {
            hir::Block{rules: UnsafeBlock(UserProvided), ref stmts, ref expr, ref id, ref span} =>
                self.visit_unsafe_block_post(stmts, expr, *id, *span),
            _ => { },
        };
    }

    fn visit_item(&mut self, i: &'v hir::Item) {
        match i.node {
            hir::Item_::ItemImpl(Unsafety::Unsafe,
                                 ref polarity,
                                 ref generics,
                                 ref trait_ref,
                                 ref self_ty,
                                 ref items) =>
                self.visit_unsafe_impl(polarity, generics, trait_ref, self_ty, items),
            hir::Item_::ItemForeignMod(ref module) => self.visit_foreign_mod(module),
            _ => {},
        }
        intravisit::walk_item(self, i);
    }
    fn visit_fn(&mut self,
                fk: intravisit::FnKind<'v>,
                fd: &'v hir::FnDecl,
                b: &'v hir::Block,
                s: Span,
                id: ast::NodeId) {
        use ::rustc::hir::intravisit::FnKind::{ItemFn,Method,Closure};
        match fk {
            ItemFn(name, generics, Unsafety::Unsafe, constness, abi, vis, attrs) =>
                self.visit_unsafe_fn(
                    FnMethodInfo::new(name, generics, constness, abi, fd, b, attrs, id, s),
                    vis
                ),
            Method(name,
                   &hir::MethodSig {
                       unsafety: Unsafety::Unsafe,
                       constness,
                       abi,
                       ref generics, .. },
                   vis,
                   ref attrs) =>
                self.visit_unsafe_method(
                    FnMethodInfo::new(name, generics, constness, abi, fd, b, attrs, id, s),
                    vis
                ),
            Closure(attrs) => self.visit_closure(fd, b, s, attrs, id),
            _ => {}
        };
        walk_gen_fn(self, fk, fd, b, s, id);
    }
    fn visit_fn_post(&mut self,
                     fk: intravisit::FnKind<'v>,
                     fd: &'v hir::FnDecl,
                     b: &'v hir::Block,
                     s: Span,
                     id: ast::NodeId) {
        use ::rustc::hir::intravisit::FnKind::{ItemFn,Method,Closure};
        match fk {
            ItemFn(name, generics, Unsafety::Unsafe, constness, abi, vis, attrs) =>
                self.visit_unsafe_fn_post(
                    FnMethodInfo::new(name, generics, constness, abi, fd, b, attrs, id, s),
                    vis
                ),
            Method(name,
                   &hir::MethodSig {
                       unsafety: Unsafety::Unsafe,
                       constness,
                       abi,
                       ref decl,
                       ref generics },
                   vis,
                   ref attrs) =>
                self.visit_unsafe_method_post(
                    FnMethodInfo::new(name, generics, constness, abi, fd, b, attrs, id, s),
                    vis
                ),
            Closure(attrs) => self.visit_closure_post(fd, b, s, attrs, id),
            _ => { /* Nothing to do */ }
        }
    }
}
pub fn walk_gen_fn<'a, 'b, 'tcx: 'a, 'v, V> (visitor: &mut V,
                                       function_kind: intravisit::FnKind<'v>,
                                       function_declaration: &'v hir::FnDecl,
                                       function_body: &'v hir::Block,
                                       _span: Span,
                                       id: ast::NodeId)
        where V: VisitUnsafe<'a, 'tcx, 'b, 'v>
{
    intravisit::walk_fn(visitor, function_kind, function_declaration, function_body, _span);
    visitor.visit_fn_post(function_kind, function_declaration, function_body, _span, id);
}

//fn walk_closure<'v, V: VisitUnsafe<'v>>(visitor: &mut V,
//                     fn_decl: &'v hir::FnDecl,
//                     block: &'v hir::Block,
//                     span: Span,
//                     attrs: &'v [ast::Attribute]) {
//    walk_gen_fn(visitor, intravisit::FnKind::Closure(attrs), fn_decl, block, span)
//}
//
//fn walk_method<'v, V: VisitUnsafe<'v>>(visitor: &mut V,
//                                       method_info: FnMethodInfo<'v>,
//                                       vis: Option<&'v hir::Visibility>) {
//    walk_gen_fn(
//        visitor,
//        intravisit::FnKind::Method(
//            method_info.name,
//            hir::MethodSig {
//                constness: method_info.constness,
//                abi: method_info.abi,
//                decl: method_info.method_decl,
//                generics: method_info.generics,
//                unsafety: Unsafety::Unsafe,
//            },
//            vis,
//            method_info.attrs),
//        method_info.method_decl,
//        method_info.block,
//        method_info.span)
//}
//
//fn walk_fn_item<'v, V: VisitUnsafe<'v>>(visitor: &mut V,
//                                        fn_info: FnMethodInfo<'v>,
//                                        vis: Option<&'v hir::Visibility>) {
//    walk_gen_fn(
//        visitor,
//        intravisit::FnKind::ItemFn(
//            fn_info.name,
//            fn_info.generics,
//            Unsafety::Unsafe,
//            fn_info.abi,
//            vis,
//            fn_info.attrs),
//        fn_info.fn_decl,
//        fn_info.block,
//        fn_info.span)
//}

pub struct FnMethodInfo<'v> {
    name: ast::Name,
    generics: &'v hir::Generics,
    constness: hir::Constness,
    abi: abi::Abi,
    fn_decl: &'v hir::FnDecl,
    block: &'v hir::Block,
    attrs: &'v [ast::Attribute],
    id: ast::NodeId,
    span: Span,
}

impl<'v> FnMethodInfo<'v> {
    pub fn new(name: ast::Name,
           generics: &'v hir::Generics,
           constness: hir::Constness,
           abi: abi::Abi,
           fn_decl: &'v hir::FnDecl,
           block: &'v hir::Block,
           attrs: &'v [ast::Attribute],
           id: ast::NodeId,
           span: Span) -> FnMethodInfo<'v> {
        FnMethodInfo {
            name: name,
            generics: generics,
            constness: constness,
            abi: abi,
            fn_decl: fn_decl,
            block: block,
            attrs: attrs,
            id: id,
            span: span,
        }
    }
}
