#![feature(rustc_attrs)]
#![allow(dead_code,unused_assignments)]

pub fn bad(public: [*const i32; 1]) -> i32 {
    //~^ WARN critical argument `public`
    let mut q: [*const i32; 1] = [0 as *const _];
    {
        let p = &mut q;
        *p = public;
    }
    unsafe { *q[0] }
}

#[rustc_error]
fn main() {} //~ ERROR compilation successful
