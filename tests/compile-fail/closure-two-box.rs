#![allow(dead_code)]
#![feature(rustc_attrs)]

#[rustc_error]
fn main() {} //~ ERROR compilation successful

// This example shows the impact of boxing closures.

pub fn bad(p: *const i32, b: bool) -> i32 {
    //~^ WARN critical argument `p`
    let x = 5;
    let danger = || p;
    let safe = || &x as *const _;
    let maybe = if b {
        Box::new(safe) as Box<Fn() -> *const i32>
    } else {
        Box::new(danger) as Box<Fn() -> *const i32>
    };
    let q = maybe();
    unsafe { *q }
}
