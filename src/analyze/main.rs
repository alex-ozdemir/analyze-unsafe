#![feature(rustc_private)]
// Alex Ozdemir <aozdemir@hmc.edu>
// Tool for counting unsafe invocations in an AST

extern crate getopts;
extern crate syntax;
extern crate rustc;
extern crate rustc_driver;

use std::path::PathBuf;
use syntax::{abi,ast,diagnostics};
use rustc::hir;
use rustc::hir::intravisit as visit;
use rustc::ty;
use rustc::session::{config,Session};
use rustc_driver::{driver,CompilerCalls,RustcDefaultCalls,Compilation};

use std::io::Write;

macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

fn count_unsafe<'a,'tcx>(krate: &hir::Crate, tcx: ty::TyCtxt<'a,'tcx,'tcx>) -> UnsafeData {
    let mut v = UnsafeVisitor::new(tcx, krate);
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

struct UnsafeVisitor<'a, 'tcx: 'a, 'b> {
    data: UnsafeData,
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    krate: &'b hir::Crate,
    has_ffi: bool,
    has_unsafe_fn: bool,
}

impl<'a,'tcx:'a,'b> UnsafeVisitor<'a,'tcx,'b> {
    fn new(tcx: ty::TyCtxt<'a,'tcx,'tcx>, krate: &'b hir::Crate) -> UnsafeVisitor<'a,'tcx,'b> {
        UnsafeVisitor {
            data: UnsafeData::new(),
            tcx: tcx,
            krate: krate,
            has_ffi: false,
            has_unsafe_fn: false,
        }
    }
}

impl<'v, 'a, 'tcx, 'b> visit::Visitor<'v> for UnsafeVisitor<'a,'tcx,'b> {
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
        visit::walk_expr(self, expr);
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
        visit::walk_item(self, i)
    }
    fn visit_fn(&mut self,
                fk: visit::FnKind<'v>,
                fd: &'v hir::FnDecl,
                b: &'v hir::Block,
                s: syntax::codemap::Span,
                _: ast::NodeId) {
        match fk {
            visit::FnKind::ItemFn(_, _, unsafety, _, _, _, _) => {
                if let hir::Unsafety::Unsafe = unsafety {
                    self.data.functions.unsaf += 1;
                }
                self.data.functions.total += 1;
            },
            visit::FnKind::Method(_, &hir::MethodSig{ unsafety, ..}, _, _) => {
                if let hir::Unsafety::Unsafe = unsafety {
                    self.data.methods.unsaf += 1;
                }
                self.data.methods.total += 1;
            },
            visit::FnKind::Closure(_) => {
                // Closures cannot be declared unsafe
                // TODO(aozdemir): There is some interesting work to do here.
            }
        }
        visit::walk_fn(self, fk, fd, b, s)
    }
}

struct AnalyzeUnsafe(RustcDefaultCalls,bool);

impl<'a> CompilerCalls<'a> for AnalyzeUnsafe {
    fn early_callback(&mut self,
                      matches: &getopts::Matches,
                      sopts: &config::Options,
                      descriptions: &diagnostics::registry::Registry,
                      output: config::ErrorOutputType)
                      -> Compilation {
        self.0.early_callback(matches, sopts, descriptions, output)
    }
    fn no_input(&mut self,
                matches: &getopts::Matches,
                sopts: &config::Options,
                odir: &Option<PathBuf>,
                ofile: &Option<PathBuf>,
                descriptions: &diagnostics::registry::Registry)
                -> Option<(config::Input, Option<PathBuf>)> {
        self.0.no_input(matches, sopts, odir, ofile, descriptions)
    }

    fn late_callback(&mut self,
                     matches: &getopts::Matches,
                     sess: &Session,
                     input: &config::Input,
                     odir: &Option<PathBuf>,
                     ofile: &Option<PathBuf>)
                     -> Compilation {
        if let &Some(ref dir) = odir {
            if let Some(dir_name) = dir.file_name() {
                if dir_name == "deps" {
                    self.1 = false;
                }
            }
        }
        self.0.late_callback(matches, sess, input, odir, ofile)
    }
    fn build_controller(
        &mut self,
        sess: &Session,
        matches: &getopts::Matches
    ) -> driver::CompileController<'a> {
        let mut control = self.0.build_controller(sess, matches);
        let do_analysis = self.1;
        let original_after_analysis_callback = control.after_analysis.callback;
        control.after_analysis.callback = Box::new(move |state| {
            if do_analysis {
                let krate = state.hir_crate.expect("HIR should exist");
                let tcx = state.tcx.expect("Type context should exist");
                let UnsafeData {
                    unsafe_blocks_no_ffi,
                    unsafe_blocks_no_unsafe_fn,
                    blocks,
                    functions,
                    methods,
                    impls,
                    declares_ffi,
                } = count_unsafe(krate, tcx);
                errln!("ANALYSIS: {} {} {}/{}/{}/{} {}/{} {}/{} {}/{} {}",
                         state.crate_name.unwrap_or("????"),
                         state.session.opts.crate_types.iter().next().map(|t| format!("{:?}",t)).unwrap_or("????".to_string()),
                         unsafe_blocks_no_unsafe_fn,
                         unsafe_blocks_no_ffi,
                         blocks.unsaf, blocks.total,
                         functions.unsaf, functions.total,
                         methods.unsaf, methods.total,
                         impls.unsaf, impls.total,
                         declares_ffi
                         );
                original_after_analysis_callback(state);
            }
        });

//        let original_after_parse_callback = control.after_parse.callback;
//        control.after_parse.callback = Box::new(move |state| {
//            let mut hi = state;
//            let mut hi2 = hi.session;
//            let mut hi3 = hi2.opts;
//            if save_ast { hi.session.opts.debugging_opts.keep_ast = true; }
//            original_after_parse_callback(hi);
//        });
        control
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut analyzer = AnalyzeUnsafe(RustcDefaultCalls, true);
    rustc_driver::run_compiler(&args, &mut analyzer);
}
