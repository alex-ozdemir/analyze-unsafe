// Alex Ozdemir <aozdemir@hmc.edu>
// Tool for counting unsafe invocations in an AST
#![feature(rustc_private)]

extern crate getopts;
extern crate syntax;
extern crate rustc;
extern crate rustc_driver;

use syntax::ast;
use syntax::visit;
use rustc::session::Session;
use rustc_driver::{driver, CompilerCalls, Compilation};

fn count_unsafe(krate: &ast::Crate) -> UnsafeData {
    let mut v = UnsafeVisitor::new();
    visit::walk_crate(&mut v, krate);
    v.data
}

#[derive(Debug,PartialEq)]
struct Counts {
    total: u64,
    unsaf: u64,
}
impl Counts { fn new() -> Counts { Counts {total: 0, unsaf: 0} } }

#[derive(Debug,PartialEq)]
struct UnsafeData {
    blocks: Counts,
    functions: Counts,
    methods: Counts,
    impls: Counts,
}

impl UnsafeData {
    fn new() -> UnsafeData {
        UnsafeData {
            blocks: Counts::new(),
            functions: Counts::new(),
            methods: Counts::new(),
            impls: Counts::new(),
        }
    }
}

unsafe impl Send for UnsafeData {}

struct UnsafeVisitor {
    data: UnsafeData
}

impl UnsafeVisitor {
    fn new() -> UnsafeVisitor {
        UnsafeVisitor { data: UnsafeData::new() }
    }
}

impl<'v> visit::Visitor<'v> for UnsafeVisitor {
    fn visit_block(&mut self, b: &ast::Block) {
        use syntax::ast::BlockCheckMode::Unsafe;
        use syntax::ast::UnsafeSource::UserProvided;
        self.data.blocks.total += 1;
        if let ast::Block{rules: Unsafe(UserProvided), ..} = *b
            { self.data.blocks.unsaf += 1; }
        visit::walk_block(self, b);
    }
    // Since unsafe blocks can live within macros uses, we traverse their interior
    fn visit_mac(&mut self, _mac: &'v ast::Mac) {
        visit::walk_mac(self, _mac)
    }
    fn visit_item(&mut self, i: &'v ast::Item) {
        if let ast::ItemKind::Impl(unsafety,_ ,_ ,_, _, _) = i.node {
            if unsafety == ast::Unsafety::Unsafe {
                self.data.impls.unsaf += 1;
            }
            self.data.impls.total += 1;
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
            }
        }
        visit::walk_fn(self, fk, fd, b, s)
    }
}

struct AnalyzeUnsafe {
    crate_name: String,
    target_name: String,
    target_type: String
}

impl<'a> CompilerCalls<'a> for AnalyzeUnsafe {
    fn build_controller(
        &mut self,
        _: &Session,
        _: &getopts::Matches
    ) -> driver::CompileController<'a> {
        let mut control = driver::CompileController::basic();

        let crate_name = self.crate_name.clone();
        let target_name = self.target_name.clone();
        let target_type = self.target_type.clone();
        control.after_parse.callback = Box::new(move |state| {
            let UnsafeData {
                blocks,
                functions,
                methods,
                impls
            } = count_unsafe(state.krate.as_ref().unwrap());
            println!("{} {} {} {}/{} {}/{} {}/{} {}/{}",
                     crate_name,
                     target_name,
                     target_type,
                     blocks.unsaf, blocks.total,
                     functions.unsaf, functions.total,
                     methods.unsaf, methods.total,
                     impls.unsaf, impls.total);
        });
        control.after_parse.stop = Compilation::Stop;

        control
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    let mut analyzer = AnalyzeUnsafe {
        crate_name: args.remove(1),
        target_name: args.remove(1),
        target_type: args.remove(1),
    };
    rustc_driver::run_compiler(&args, &mut analyzer);
}
