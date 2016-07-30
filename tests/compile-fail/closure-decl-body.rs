#![allow(dead_code)]
#![feature(rustc_attrs)]

#[rustc_error]
fn main() {} //~ ERROR compilation successful

pub fn flow_out_closure(p: *const i32) -> i32 {
    let id = || p;
    let q = id();
    unsafe { *q }
}
