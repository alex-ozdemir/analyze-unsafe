#![allow(dead_code)]
#![feature(rustc_attrs)]

pub fn bad(i: *const i64) -> i64 {
    //~^ WARNING critical argument `i`
    unsafe { *i }
}

#[rustc_error]
fn main() {} //~ ERROR compilation successful
