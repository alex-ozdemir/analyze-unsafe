#![allow(dead_code,unused_assignments)]

pub fn bad(public: [*const i32; 1]) -> i32 {
    let mut q: [*const i32; 1] = [0 as *const _];
    {
        let p = &mut q;
        *p = public;
    }
    unsafe { *q[0] }
}

fn main() {}
