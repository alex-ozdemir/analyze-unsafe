#![feature(box_patterns,rustc_private)]
// Alex Ozdemir <aozdemir@hmc.edu>
// Tool for counting unsafe invocations in an AST

extern crate getopts;
extern crate syntax;
#[macro_use] extern crate rustc;
extern crate rustc_driver;
extern crate rustc_serialize;
extern crate rustc_data_structures;

mod summarize;
mod dataflow;
mod count;
mod back;

use count::UnsafeData;

use back::{EscapeAnalysis,BackwardsAnalysis};

use rustc_serialize::json;

use rustc::hir;
use rustc::hir::intravisit;
use rustc::ty;
use rustc::session::{config,Session};

use rustc_driver::{driver,CompilerCalls,RustcDefaultCalls,Compilation};
use rustc_driver::driver::CompileState;

use syntax::diagnostics;

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::io::Write;
use std::mem;
use std::path::PathBuf;

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

fn summarize_unsafe<'a,'tcx>(krate: &hir::Crate, tcx: ty::TyCtxt<'a,'tcx,'tcx>) {
    let mut v = summarize::UnsafeSummarizer::new(tcx);
    krate.visit_all_items(&mut v);
    errln!("JSON:{}", json::as_json(&v.functions));
    errln!("RUST:{:?}", v.functions);
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

    pub fn unsafe_ast_emitter() -> AnalyzeUnsafe<'a> {
        AnalyzeUnsafe::new(Box::new(move |state| {
            let krate = state.hir_crate.expect("HIR should exist");
            let tcx = state.tcx.expect("Type context should exist");
            summarize_unsafe(krate, tcx);
        }))
    }

    pub fn dataflow() -> AnalyzeUnsafe<'a> {
        AnalyzeUnsafe::new(Box::new(move |state| {
            let analysis = state.analysis.unwrap();
            let hir = state.hir_crate.unwrap();
            let tcx = state.tcx.expect("Type context should exist");
            let mir_map = state.mir_map.expect("We should be in orbit - use `-Z orbit`");
            let escape_analysis = EscapeAnalysis::flow(mir_map, tcx);
            escape_analysis.get_lints(analysis, hir).iter().map(|&(span, ref err)|
                state.session.span_warn(span, err)
            ).count();
        }))
    }
}

impl<'a,'callback: 'a> CompilerCalls<'a> for AnalyzeUnsafe<'callback> {
    fn early_callback(&mut self,
                      matches: &getopts::Matches,
                      sopts: &config::Options,
                      descriptions: &diagnostics::registry::Registry,
                      output: config::ErrorOutputType)
                      -> Compilation {
        self.default.early_callback(matches, sopts, descriptions, output)
    }

    fn no_input(&mut self,
                matches: &getopts::Matches,
                sopts: &config::Options,
                odir: &Option<PathBuf>,
                ofile: &Option<PathBuf>,
                descriptions: &diagnostics::registry::Registry)
                -> Option<(config::Input, Option<PathBuf>)> {
        self.default.no_input(matches, sopts, odir, ofile, descriptions)
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
                    self.do_analysis = false;
                }
            }
        }
        self.default.late_callback(matches, sess, input, odir, ofile)
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
            if do_analysis {
                (*callback)(state);
                original_after_analysis_callback(state);
            }
        });
        control
    }
}


#[allow(dead_code)]
fn print_map_lines<K: Debug + Eq + Hash, V: Debug>(map: &HashMap<K, V>) {
    println!("Map:");
    for (key, val) in map.iter() {
        println!("  {:?} : {:?}", key, val);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut analyzer = AnalyzeUnsafe::dataflow();
    rustc_driver::run_compiler(&args, &mut analyzer);
}
