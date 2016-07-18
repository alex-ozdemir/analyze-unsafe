#![allow(dead_code)]

pub fn bad(i: *const i64) -> i64 {
    unsafe { *i }
}

fn main() {}
