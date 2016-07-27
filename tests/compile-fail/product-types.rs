#![feature(rustc_attrs)]
#![allow(dead_code)]

pub struct Pair(pub *const i32, pub *const i32);

pub struct Point {
    pub x: *const i32,
    pub y: *const i32,
}

pub struct PrivatePair(*const i32, *const i32);

pub struct PrivatePoint {
    x: *const i32,
    y: *const i32,
}

pub fn bad10(p: (*const i32, *const i32)) -> i32 {
    //~^ WARN critical argument `(p.0#1)`
    unsafe { *(p.1) }
}

pub fn bad11(i: (*const i64, i64)) -> i64 {
    //~^ WARN critical argument `(i.0#0)`
    unsafe { *(i.0) }
}

pub fn bad12(p: (*const i32, *const i32)) -> i32 {
    //~^ WARN critical arguments `(p.0#0)`, `(p.0#1)`
    (unsafe { *(p.1) }) + (unsafe { *(p.0) })
}

pub fn bad13(p: (*const i32, *const i32)) -> i32 {
    //~^ WARN critical arguments `(p.0#0)`, `(p.0#1)`
    let q = p.0;
    (unsafe { *(p.1) }) + (unsafe { *q })
}

pub fn okay14(i: (*const i64, i64)) -> i64 {
    i.1
}

fn okay15(mut i: (*const i64, i64)) -> i64 {
    //TODO: Be more precise, then make this public!
    i.0 = &(i.1);
    unsafe { *(i.0) }
}

pub fn bad20(p: Pair) -> i32 {
    //~^ WARN critical argument `(p.0#0)`
    unsafe { *(p.0) }
}

pub fn ok21(p: PrivatePair) -> i32 {
    unsafe { *(p.0) }
}

pub fn ok31(p: PrivatePoint) -> i32 {
    unsafe { *(p.x) }
}

#[rustc_error]
fn main(){ } //~ERROR compilation successful
