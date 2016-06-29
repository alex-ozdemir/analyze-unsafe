#![allow(dead_code)]

pub struct Pair(*const i32, *const i32);

pub struct Point {
    x: *const i32,
    y: *const i32,
}

pub fn bad10(p: (*const i32, *const i32)) -> i32 {
    unsafe { *(p.1) }
}

pub fn bad11(i: (*const i64, i64)) -> i64 {
    unsafe { *(i.0) }
}

pub fn bad12(p: (*const i32, *const i32)) -> i32 {
    (unsafe { *(p.1) }) + (unsafe { *(p.0) })
}

pub fn bad13(p: (*const i32, *const i32)) -> i32 {
    let q = p.0;
    (unsafe { *(p.1) }) + (unsafe { *q })
}

pub fn okay14(i: (*const i64, i64)) -> i64 {
    i.1
}

pub fn okay15(mut i: (*const i64, i64)) -> i64 {
    i.0 = &(i.1);
    unsafe { *(i.0) }
}

pub fn bad20(p: Pair) -> i32 {
    unsafe { *(p.0) }
}

pub fn bad30(p: Point) -> i32 {
    unsafe { *(p.x) }
}

fn main(){ }

