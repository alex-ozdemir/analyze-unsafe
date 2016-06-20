#![allow(dead_code)]
fn id1(p: *const i32) -> *const i32 {
    let pp: *const *const i32 = &p;
    unsafe { *pp } // Ok
}

fn id2(p: *const i32) -> i32 {
    let pp: *const *const i32 = &p;
    unsafe { **pp } // Not Okay
}

fn main() { println!("hi"); }
