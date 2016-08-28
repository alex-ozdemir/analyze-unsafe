#![feature(box_syntax,box_patterns,rustc_private)]
// Alex Ozdemir <aozdemir@hmc.edu>
// Tool for counting unsafe invocations in an AST

extern crate getopts;
extern crate syntax;
#[macro_use] extern crate rustc;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate syntax_pos;
extern crate serialize;
extern crate rustc_data_structures;

mod count;
mod backflow;
mod complex;
mod base_var;
mod dep_graph;
mod path;
mod transfer;

use count::UnsafeData;

use complex::ComplexEscapeAnalysis;

use backflow::BackwardsAnalysis;

use rustc::hir;
use rustc::hir::intravisit;
use rustc::ty;
use rustc::session::{config,Session};

use rustc_driver::{driver,CompilerCalls,RustcDefaultCalls,Compilation};
use rustc_driver::driver::CompileState;

use syntax::ast;

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::mem;
use std::path::PathBuf;

use std::io::Write;
macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

fn count_unsafe<'a,'tcx>(krate: &hir::Crate, tcx: ty::TyCtxt<'a,'tcx,'tcx>) -> UnsafeData {
    let mut v = count::UnsafeCounter::new(tcx, krate);
    intravisit::walk_crate(&mut v, krate);
    v.data
}

/// A complier calls structure which behaves like Rustc, less running a callback
/// post-analysis.
pub struct AnalyzeUnsafe<'a> {
    default: RustcDefaultCalls,
    do_analysis: bool,
    after_analysis_callback: Box<Fn(&mut CompileState) + 'a>,
}

impl<'a> AnalyzeUnsafe<'a> {
    pub fn new(after_analysis_callback: Box<Fn(&mut CompileState) + 'a>) -> AnalyzeUnsafe<'a> {
        AnalyzeUnsafe {
            default: RustcDefaultCalls,
            do_analysis: true,
            after_analysis_callback: after_analysis_callback,
        }
    }

    pub fn statistic_collector() -> AnalyzeUnsafe<'a> {
        AnalyzeUnsafe::new(Box::new(move |state| {
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
            let crate_type = state.session.opts.crate_types.iter().next().map(|t| format!("{:?}",t));
            errln!("ANALYSIS: {} {} {}/{}/{}/{} {}/{} {}/{} {}/{} {}",
                   state.crate_name.unwrap_or("????"),
                   crate_type.unwrap_or("????".to_string()),
                   unsafe_blocks_no_unsafe_fn,
                   unsafe_blocks_no_ffi,
                   blocks.unsaf, blocks.total,
                   functions.unsaf, functions.total,
                   methods.unsaf, methods.total,
                   impls.unsaf, impls.total,
                   declares_ffi
            );
        }))
    }

    pub fn dataflow() -> AnalyzeUnsafe<'a> {
        AnalyzeUnsafe::new(Box::new(move |state| {
            let analysis = state.analysis.unwrap();
            //let hir_map = state.ast_map.unwrap();
            let hir = state.hir_crate.unwrap();
            let tcx = state.tcx.expect("Type context should exist");
            let mir_map = state.mir_map.expect("We should be in orbit - use `-Z orbit`");
            errln!("Spinning up analysis. Mir count: {}", mir_map.map.keys().len());
            let escape_analysis = ComplexEscapeAnalysis::flow(mir_map, tcx, analysis.clone());
            for (au, map) in escape_analysis.context_and_fn_to_fact_map.iter() {
                errln!("{:?} ", au);
                print_map_lines(map);
            }
            escape_analysis.get_lints(/* hir_map, */hir).iter().map(|&(span, ref err)|
                state.session.span_warn(span, err)
            ).count();
        }))
    }
}

impl<'a,'callback: 'a> CompilerCalls<'a> for AnalyzeUnsafe<'callback> {
    fn early_callback(&mut self,
                      matches: &getopts::Matches,
                      sopts: &config::Options,
                      cfg: &ast::CrateConfig,
                      descriptions: &rustc_errors::registry::Registry,
                      output: config::ErrorOutputType)
                      -> Compilation {
        self.default.early_callback(matches, sopts, cfg, descriptions, output)
    }

    fn no_input(&mut self,
                matches: &getopts::Matches,
                sopts: &config::Options,
                cfg: &ast::CrateConfig,
                odir: &Option<PathBuf>,
                ofile: &Option<PathBuf>,
                descriptions: &rustc_errors::registry::Registry)
                -> Option<(config::Input, Option<PathBuf>)> {
        self.default.no_input(matches, sopts, cfg, odir, ofile, descriptions)
    }

    fn late_callback(&mut self,
                     matches: &getopts::Matches,
                     sess: &Session,
                     cfg: &ast::CrateConfig,
                     input: &config::Input,
                     odir: &Option<PathBuf>,
                     ofile: &Option<PathBuf>)
                     -> Compilation {
        if let &Some(ref dir) = odir {
            if let Some(dir_name) = dir.file_name() {
                if dir_name == "deps" {
                    self.do_analysis = false;
                }
            }
        }
        self.default.late_callback(matches, sess, cfg, input, odir, ofile)
    }

    fn build_controller(
        &mut self,
        sess: &Session,
        matches: &getopts::Matches
    ) -> driver::CompileController<'a> {

        let mut control = self.default.build_controller(sess, matches);
        let callback = mem::replace(&mut self.after_analysis_callback, Box::new(|_| {}));
        let original_after_analysis_callback = control.after_analysis.callback;
        let do_analysis = self.do_analysis;
        control.after_analysis.callback = Box::new(move |state| {
            state.session.abort_if_errors();
            if true {
                (*callback)(state);
                original_after_analysis_callback(state);
            }
        });
        control
    }
}


#[allow(dead_code)]
fn print_map_lines<K: Debug + Eq + Ord, V: Debug>(map: &BTreeMap<K, V>) {
    errln!("Map:");
    for (key, val) in map.iter() {
        errln!("  {:?} : {:?}", key, val);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut analyzer = AnalyzeUnsafe::dataflow();
    rustc_driver::run_compiler(&args, &mut analyzer);
}
