// Alex Ozdemir <aozdemir@hmc.edu>
// Tool for counting unsafe invocations in an AST
#![feature(rustc_private)]

extern crate getopts;
extern crate syntax;
extern crate rustc;
extern crate rustc_driver;

use syntax::{abi,ast,visit};
//use rustc::hir;
//use rustc::hir::intravisit as hir_visit;
use rustc::ty;
use rustc::session::Session;
use rustc_driver::{driver, CompilerCalls, Compilation};

fn count_unsafe<'a,'tcx>(krate: &ast::Crate, tcx: ty::TyCtxt<'a,'tcx,'tcx>) -> UnsafeData {
    let mut v = UnsafeVisitor::new(tcx);
    visit::walk_crate(&mut v, krate);
    v.data
}

#[derive(Debug,PartialEq)]
struct Counts {
    unsaf: u64,
    total: u64,
}
impl Counts { fn new() -> Counts { Counts {total: 0, unsaf: 0} } }

#[derive(Debug,PartialEq)]
struct UnsafeData {
    unsafe_blocks_no_ffi: u64,
    unsafe_blocks_no_unsafe_fn: u64,
    blocks: Counts,
    functions: Counts,
    methods: Counts,
    impls: Counts,
    declares_ffi: bool,
}

impl UnsafeData {
    fn new() -> UnsafeData {
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

unsafe impl Send for UnsafeData {}

struct UnsafeVisitor<'a, 'tcx: 'a> {
    data: UnsafeData,
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    has_ffi: bool,
    has_unsafe_fn: bool,
}

impl<'b,'tcx:'b> UnsafeVisitor<'b,'tcx> {
    fn new(tcx: ty::TyCtxt<'b,'tcx,'tcx>) -> UnsafeVisitor<'b,'tcx> {
        UnsafeVisitor {
            data: UnsafeData::new(),
            tcx: tcx,
            has_ffi: false,
            has_unsafe_fn: false,
        }
    }
}

impl<'v, 'b, 'tcx> visit::Visitor<'v> for UnsafeVisitor<'b,'tcx> {
    fn visit_block(&mut self, b: &ast::Block) {
        use syntax::ast::BlockCheckMode::Unsafe;
        use syntax::ast::UnsafeSource::UserProvided;

        self.data.blocks.total += 1;

        let is_unsafe_block = match *b {
            ast::Block{rules: Unsafe(UserProvided), ..} => true,
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

        visit::walk_block(self, b);

        // After the dive, update our statistics and reload state if we saved it.
        if is_unsafe_block {
            self.data.blocks.unsaf += 1;
            if !self.has_ffi {self.data.unsafe_blocks_no_ffi += 1;}
            if !self.has_unsafe_fn {self.data.unsafe_blocks_no_unsafe_fn += 1;}
            self.has_ffi = old_ffi;
            self.has_unsafe_fn = old_unsafe_fn
        }
    }
    fn visit_expr(&mut self, expr: &'v ast::Expr) {
        use rustc::hir::Unsafety;
        if let ast::ExprKind::Call(ref ptr_expr, _) = expr.node {
            let tys = self.tcx.node_id_to_type(ptr_expr.id);
            if let ty::TyFnDef(_, _,
                               &ty::BareFnTy{unsafety, abi, ..}) = tys.sty {

                if unsafety == Unsafety::Unsafe { self.has_unsafe_fn = true; }

                if abi != abi::Abi::Rust { self.has_ffi = true; }
            };
        };
        visit::walk_expr(self, expr);
    }
    fn visit_item(&mut self, i: &'v ast::Item) {
        if let ast::ItemKind::Impl(unsafety,_ ,_ ,_, _, _) = i.node {
            if unsafety == ast::Unsafety::Unsafe {
                self.data.impls.unsaf += 1;
            }
            self.data.impls.total += 1;
        }
        if let ast::ItemKind::ForeignMod(_) = i.node {
            self.data.declares_ffi = true;
        }
        visit::walk_item(self, i)
    }
    fn visit_fn(&mut self,
                fk: visit::FnKind<'v>,
                fd: &'v ast::FnDecl,
                b: &'v ast::Block,
                s: syntax::codemap::Span,
                _: ast::NodeId) {
        match fk {
            visit::FnKind::ItemFn(_, _, unsafety, _, _, _) => {
                if let ast::Unsafety::Unsafe = unsafety {
                    self.data.functions.unsaf += 1;
                }
                self.data.functions.total += 1;
            },
            visit::FnKind::Method(_, &ast::MethodSig{ unsafety, ..}, _) => {
                if let ast::Unsafety::Unsafe = unsafety {
                    self.data.methods.unsaf += 1;
                }
                self.data.methods.total += 1;
            },
            visit::FnKind::Closure => {
                // Closures cannot be declared unsafe
                // TODO(aozdemir): There is some interesting work to do here.
            }
        }
        visit::walk_fn(self, fk, fd, b, s)
    }
}

struct AnalyzeUnsafe;

impl<'a> CompilerCalls<'a> for AnalyzeUnsafe {
    fn build_controller(
        &mut self,
        _: &Session,
        _: &getopts::Matches
    ) -> driver::CompileController<'a> {
        let mut control = driver::CompileController::basic();

        control.after_analysis.callback = Box::new(move |state| {
            if let Some(krate) = state.expanded_crate {
                let tcx = state.tcx.expect("no type context");
                let UnsafeData {
                    unsafe_blocks_no_ffi,
                    unsafe_blocks_no_unsafe_fn,
                    blocks,
                    functions,
                    methods,
                    impls,
                    declares_ffi,
                } = count_unsafe(krate, tcx);
                println!("{} {}/{}/{}/{} {}/{} {}/{} {}/{} {}",
                         state.crate_name.expect("no crate name"),
                         unsafe_blocks_no_unsafe_fn,
                         unsafe_blocks_no_ffi,
                         blocks.unsaf, blocks.total,
                         functions.unsaf, functions.total,
                         methods.unsaf, methods.total,
                         impls.unsaf, impls.total,
                         declares_ffi
                         );
            }
        });
        control.after_analysis.stop = Compilation::Stop;

        control
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut analyzer = AnalyzeUnsafe;
    rustc_driver::run_compiler(&args, &mut analyzer);
}
