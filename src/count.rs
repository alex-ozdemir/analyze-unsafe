use syntax::{ast,abi};
use syntax::codemap::Span;
use rustc::hir;
use rustc::hir::intravisit;
use rustc::ty;

#[derive(Debug,PartialEq)]
pub struct Counts {
    pub unsaf: u64,
    pub total: u64,
}
impl Counts { fn new() -> Counts { Counts {total: 0, unsaf: 0} } }

#[derive(Debug,PartialEq)]
pub struct UnsafeData {
    pub unsafe_blocks_no_ffi: u64,
    pub unsafe_blocks_no_unsafe_fn: u64,
    pub blocks: Counts,
    pub functions: Counts,
    pub methods: Counts,
    pub impls: Counts,
    pub declares_ffi: bool,
}

impl UnsafeData {
    pub fn new() -> UnsafeData {
        UnsafeData {
            unsafe_blocks_no_unsafe_fn: 0,
            unsafe_blocks_no_ffi: 0,
            blocks: Counts::new(),
            functions: Counts::new(),
            methods: Counts::new(),
            impls: Counts::new(),
            declares_ffi: false,
        }
    }
}

pub struct UnsafeCounter<'a, 'tcx: 'a, 'b> {
    pub data: UnsafeData,
    pub tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    pub krate: &'b hir::Crate,
    pub has_ffi: bool,
    pub has_unsafe_fn: bool,
}

impl<'a,'tcx:'a,'b> UnsafeCounter<'a,'tcx,'b> {
    pub fn new(tcx: ty::TyCtxt<'a,'tcx,'tcx>, krate: &'b hir::Crate) -> UnsafeCounter<'a,'tcx,'b> {
        UnsafeCounter {
            data: UnsafeData::new(),
            tcx: tcx,
            krate: krate,
            has_ffi: false,
            has_unsafe_fn: false,
        }
    }
}

impl<'v, 'a, 'tcx, 'b> intravisit::Visitor<'v> for UnsafeCounter<'a,'tcx,'b> {
    fn visit_nested_item(&mut self, id: hir::ItemId) {
        let item = self.krate.items.get(&id.id).expect("ItemId should exist");
        self.visit_item(item);
    }
    fn visit_block(&mut self, b: &hir::Block) {
        use rustc::hir::BlockCheckMode::UnsafeBlock;
        use rustc::hir::UnsafeSource::UserProvided;

        self.data.blocks.total += 1;

        let is_unsafe_block = match *b {
            hir::Block{rules: UnsafeBlock(UserProvided), ..} => true,
            _ => false,
        };

        // If this block is unsafe, we want to examine it indedependent of its surroundings, so we
        // save state, reset state, and then dive in.
        // Note: this only matters for nested unsafe (which is linted against)
        let old_ffi = self.has_ffi;
        let old_unsafe_fn = self.has_unsafe_fn;
        if is_unsafe_block {
            self.has_ffi = false;
            self.has_unsafe_fn = false;
        }

        intravisit::walk_block(self, b);

        // After the dive, update our statistics and reload state if we saved it.
        if is_unsafe_block {
            self.data.blocks.unsaf += 1;
            if !self.has_ffi {self.data.unsafe_blocks_no_ffi += 1;}
            if !self.has_unsafe_fn {self.data.unsafe_blocks_no_unsafe_fn += 1;}
            self.has_ffi = old_ffi;
            self.has_unsafe_fn = old_unsafe_fn
        }
    }
    fn visit_expr(&mut self, expr: &'v hir::Expr) {
        use rustc::hir::Unsafety;
        if let hir::Expr_::ExprCall(ref ptr_expr, _) = expr.node {
            let tys = self.tcx.node_id_to_type(ptr_expr.id);
            if let ty::TyFnDef(_, _,
                               &ty::BareFnTy{unsafety, abi, ..}) = tys.sty {

                if unsafety == Unsafety::Unsafe { self.has_unsafe_fn = true; }

                if abi != abi::Abi::Rust { self.has_ffi = true; }
            };
        };
        intravisit::walk_expr(self, expr);
    }
    fn visit_item(&mut self, i: &'v hir::Item) {
        if let hir::Item_::ItemImpl(unsafety,_ ,_ ,_, _, _) = i.node {
            if unsafety == hir::Unsafety::Unsafe {
                self.data.impls.unsaf += 1;
            }
            self.data.impls.total += 1;
        }
        if let hir::Item_::ItemForeignMod(_) = i.node {
            self.data.declares_ffi = true;
        }
        intravisit::walk_item(self, i)
    }
    fn visit_fn(&mut self,
                fk: intravisit::FnKind<'v>,
                fd: &'v hir::FnDecl,
                b: &'v hir::Block,
                s: Span,
                id: ast::NodeId) {
        match fk {
            intravisit::FnKind::ItemFn(_, _, unsafety, _, _, _, _) => {
                if let hir::Unsafety::Unsafe = unsafety {
                    self.data.functions.unsaf += 1;
                }
                self.data.functions.total += 1;
            },
            intravisit::FnKind::Method(_, &hir::MethodSig{ unsafety, ..}, _, _) => {
                if let hir::Unsafety::Unsafe = unsafety {
                    self.data.methods.unsaf += 1;
                }
                self.data.methods.total += 1;
            },
            intravisit::FnKind::Closure(_) => {
                // Closures cannot be declared unsafe
                // TODO(aozdemir): There is some interesting work to do here.
            }
        }
        intravisit::walk_fn(self, fk, fd, b, s, id)
    }
}

