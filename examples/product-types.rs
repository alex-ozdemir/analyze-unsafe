#![allow(dead_code)]

pub struct Pair(*const i32, *const i32);

pub struct Point {
    x: *const i32,
    y: *const i32,
}

pub fn bad10(p: (*const i32, *const i32)) -> i32 {
    let out = unsafe { *(p.0) };
    let q = p;
    out
}

pub fn bad20(p: Pair) -> i32 {
    unsafe { *(p.0) }
}

pub fn bad30(p: Point) -> i32 {
    unsafe { *(p.x) }
}

pub fn mk_vec() {
    let v = vec![3, 4, 5];
    let y = v[0];
}

fn main(){ }

