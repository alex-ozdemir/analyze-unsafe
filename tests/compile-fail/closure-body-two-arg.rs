#![allow(dead_code)]
#![feature(rustc_attrs)]

#[rustc_error]
fn main() {} //~ ERROR compilation successful

pub fn flow_through_closure(p: *const i32) -> i32 {
    //~^ WARN critical argument `p`
    let id1 = |p: *const i32, _: *const i32| p;
    let q2 = id1(p, 0 as *const i32);
    let q = id_fn(q2);
    unsafe { *q }
}

pub fn id_fn(p: *const i32) -> *const i32 {
    p
}
