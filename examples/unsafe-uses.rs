#![feature(asm)]
#![allow(dead_code)]

#[macro_use]
extern crate lazy_static;

lazy_static! {
    static ref COUNT: usize = 5;
}

static mut TIMES: usize = 6;

unsafe fn deref() -> usize {
    let p = 0 as *const usize;
    *p
}

fn mut_static() {
    unsafe {
        TIMES += 1;
    }
}

fn inline_asm(a: i32, b: i32) -> i32 {
    let c: i32;
    unsafe {
        asm!("add $2, $0"
             : "=r"(c)
             : "0"(a), "r"(b)
             );
    }
    c
}

fn call_unsafe<'a>(a: *const i32) -> &'a i32 {
    unsafe {
        a.as_ref().unwrap()
    }
}

fn main() {}
