#![feature(rustc_attrs)]
#![allow(dead_code,unused_assignments)]

pub fn alias(public: (*const i32, i32)) -> i32 {
    //~^ WARN critical argument `(public.0#0)`
    let mut q: (*const i32, i32) = (0 as *const _, 0);
    {
        let p = &mut q;
        *p = public;
    }
    unsafe { *q.0 }
}

pub fn alias2(public: (*const i32, i32)) -> i32 {
    //~^ WARN critical argument `(public.0#0)`
    let mut q: (*const i32, i32) = (0 as *const _, 0);
    {
        let p = &mut q.0;
        *p = public.0;
    }
    unsafe { *q.0 }
}

#[rustc_error]
fn main() {} //~ ERROR compilation successful
