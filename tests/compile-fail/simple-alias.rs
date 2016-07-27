#![allow(dead_code,unused_assignments)]
#![feature(rustc_attrs)]

pub fn bad(public: *const i32) -> i32 {
    //~^ WARN critical argument `public`
    let mut q: *const i32 = 0 as *const _;
    {
        let p = &mut q;
        *p = public;
    }
    unsafe { *q }
}

#[rustc_error]
fn main() {} //~ ERROR compilation successful
