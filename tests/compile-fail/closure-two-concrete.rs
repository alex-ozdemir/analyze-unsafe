#![allow(dead_code,unused_variables)]
#![feature(rustc_attrs)]

#[rustc_error]
fn main() {} //~ ERROR compilation successful

// This example gets at the fact that closures have unique types, so unless we're turning them into
// trait objects we should have little trouble distinguishing distinct closures.

pub fn bad(p: *const i32) -> i32 {
    //~^ WARN critical argument `p`
    let x = 5;
    let danger = || p;
    let safe = || &x as *const _;
    let q = danger();
    unsafe { *q }
}

pub fn ok(p: *const i32) -> i32 {
    let x = 5;
    let danger = || p;
    let safe = || &x as *const _;
    let q = safe();
    unsafe { *q }
}
