#![allow(dead_code,unused_assignments)]
pub fn bad(public: *const i32) -> i32 {
    let mut q: *const i32 = 0 as *const _;
    {
        let p = &mut q;
        *p = public;
    }
    unsafe { *q }
}

fn main() {}
