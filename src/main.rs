#![feature(box_patterns,rustc_private)]
#![allow(unused_imports)]
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

use syntax::diagnostics;

use std::path::PathBuf;
use std::io::Write;
use std::fmt::Debug;
use std::collections::HashMap;
use std::hash::Hash;

macro_rules! errln(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

#[allow(dead_code)]
fn count_unsafe<'a,'tcx>(krate: &hir::Crate, tcx: ty::TyCtxt<'a,'tcx,'tcx>) -> UnsafeData {
    let mut v = count::UnsafeCounter::new(tcx, krate);
    intravisit::walk_crate(&mut v, krate);
    v.data
}

#[allow(dead_code)]
fn summarize_unsafe<'a,'tcx>(krate: &hir::Crate, tcx: ty::TyCtxt<'a,'tcx,'tcx>) {
    let mut v = summarize::UnsafeSummarizer::new(tcx);
    krate.visit_all_items(&mut v);
    //errln!("JSON:{}", json::as_json(&v.functions));
    //errln!("RUST:{:?}", v.functions);
}

// The defaults, and whether to do analysis or not
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
            state.session.abort_if_errors();
            if do_analysis {
                //let krate = state.hir_crate.expect("HIR should exist");
                let analysis = state.analysis.unwrap();
                let hir = state.hir_crate.unwrap();
                //println!("Exports: {:?}", analysis.export_map.keys().collect::<Vec<_>>());
                //println!("AccessLevels: {:?}", analysis.access_levels);
                let tcx = state.tcx.expect("Type context should exist");
                /*
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
                summarize_unsafe(krate, tcx);
                */
                let mir_map = state.mir_map.expect("We should be in orbit");
                //for (_, mir) in mir_map.map.iter() {
                    //for err_span in dataflow::check_for_deref_of_unknown_ptr(mir) {
                        //state.session.span_warn(err_span, "Dereference of unknown raw pointer!");
                    //}
                //}
                let escape_analysis = EscapeAnalysis::flow(mir_map, tcx);
                //println!("Printing the results of escape analysis:");
                //for (i, _) in mir_map.map.iter() {
                    //print!("Escape: {:?}: ", i);
                    //escape_analysis.crate_fact_maps_normal_return.get(&i)
                        //.map(print_map_lines);
                //}
                escape_analysis.get_concerns(analysis, hir).iter().map(|&(span, ref err)|
                    state.session.span_warn(span, err.as_str())
                ).count();
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
    let mut analyzer = AnalyzeUnsafe(RustcDefaultCalls, true);
    rustc_driver::run_compiler(&args, &mut analyzer);
}
