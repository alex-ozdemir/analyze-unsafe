#![allow(dead_code)]
#![feature(rustc_attrs)]

#[rustc_error]
fn main() {} //~ ERROR compilation successful

pub fn flow_through_closure(p: *const i32) -> i32 {
    //~^ WARN critical argument `p`
    let id: Box<Fn(_)->_> = Box::new(|p: *const i32| p);
    let q = id(p);
    unsafe { *q }
}
