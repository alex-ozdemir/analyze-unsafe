#![allow(dead_code)]
#![feature(rustc_attrs)]

#[rustc_error]
fn main() {} //~ ERROR compilation successful

pub fn flow_through_closure(p: *const i32) -> i32 {
    //~^ WARN critical argument `p`
    let q = id_fn(p);
    unsafe { *q }
}

pub fn id_fn<T>(x: T) -> T {
    x
}
