#![allow(dead_code)]

// Since you can have pointers to pointers, etc, and assign to pointers, we need to do some path
// analysis or type-based path-like analysis

pub fn maybe<T>(p: *const T) -> _ {
     let pp: *const _ = &p;
     unsafe {
        *pp   // Okay
        //**pp   Danger!
        //***pp  Type Error!
    }
}

// Okay
pub fn ok<T>(t: T) -> T {
     let p: *const _ = &t;
     unsafe { *p }
}


// Not okay
pub fn mov<T>(p: *const T, i: isize) -> T {
     let p2 = p.offset(i);
     unsafe { *p2 }
}

fn main() { println!("hi"); }
