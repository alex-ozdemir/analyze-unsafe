#![allow(dead_code)]

pub struct Pair(*const i32, *const i32);

pub struct Point {
    x: *const i32,
    y: *const i32,
}

pub fn bad10(p: (*const i32, *const i32)) -> i32 {
    unsafe { *(p.0) }
}

pub fn bad20(p: Pair) -> i32 {
    unsafe { *(p.0) }
}

pub fn bad30(p: Point) -> i32 {
    unsafe { *(p.x) }
}

fn main(){ }

