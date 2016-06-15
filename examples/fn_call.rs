#![allow(dead_code)]

fn fn_a(i: i32) -> i32 {
    fn_b(i)
}

fn fn_b(i: i32) -> i32 {
    if i < 0 {
        i + 1
    } else {
        i - 1
    }
}

fn apply1(f: fn(i32) -> i32, i: *const i32) -> i32 {
    f(unsafe {*i})
}

fn apply2(f: *const fn(i32) -> i32, i: i32) -> i32 {
    (unsafe {*f})(i)
}

fn fn_taints(f: fn(*const i32) -> *const i32, i: *const i32) -> i32 {
    let j = f(i);
    unsafe {*j}
}

fn main() { println!("hi"); }
