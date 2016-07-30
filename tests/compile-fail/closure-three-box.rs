#![allow(dead_code)]
#![feature(rustc_attrs)]

#[rustc_error]
fn main() {} //~ ERROR compilation successful

// This example limits our boxing of closures;

pub fn bad(p: *const i32) -> i32 {
    let x = 5;
    let danger = Box::new(|| p) as Box<Fn() -> *const i32>;
    let safe = Box::new(|| &x as *const _) as Box<Fn() -> *const i32>;
    let safe2 = Box::new(|| &x as *const _) as Box<Fn() -> *const i32>;
    let safe_boxed = if true {
        safe
    } else {
        safe2
    };
    let q = safe_boxed();
    unsafe { *q }
}
