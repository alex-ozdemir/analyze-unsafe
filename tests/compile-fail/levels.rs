#![feature(rustc_attrs)]
#![allow(dead_code)]

// Since you can have pointers to pointers, etc, and assign to pointers, we need to do some path
// analysis or type-based path-like analysis

pub fn ok1(p: *const i32) -> *const i32 {
    let pp: *const _ = &p;
    unsafe {
       *pp   // Okay
       //**pp   Danger!
       //***pp  Type Error!
    }
}

pub fn ohno1(p: *const i32) -> i32 {
    //~^ WARN critical argument `p`
    let pp: *const _ = &p;
    unsafe {
       **pp
    }
}

pub fn ohno3(p: &*const i32) -> i32 {
    //~^ WARN critical argument `(*p)`
    let pp: *const _ = &p;
    unsafe {
       ***pp
    }
}

// Okay
pub fn ok2(t: i32) -> i32 {
    let p: *const _ = &t;
    unsafe { *p }
}


// Depends ...
pub fn ohno2(p: *const i32, i: isize) -> i32 {
    //~^ WARN critical arguments `p`, `i`
    // TODO: be more precise!
    let p2 = unsafe{ p.offset(i) };
    unsafe { *p2 }
}

#[rustc_error]
fn main() { } //~ ERROR compilation successful
