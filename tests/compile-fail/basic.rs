#![feature(rustc_attrs)]
#![allow(dead_code)]
use std::mem;

fn meh(i: *const i64) -> i64 {
    unsafe { *i }
}

pub fn ohno1(i: *const (i64, i64)) -> i64 {
    //~^ WARNING critical argument `i`
    unsafe { (*i).0 }
}

pub fn ohno2(i: *const [i64; 5], j: usize) -> i64 {
    //~^ WARNING critical arguments `i`, `j`
    unsafe { (*i)[j] }
}

pub mod hi {
    pub fn ohno3(i: *const [i64; 5]) -> i64 {
    //~^ WARNING critical argument `i`
        unsafe { (*i)[2] }
    }
}

pub fn ohno4<'a>(i: *const i32) -> &'a i32 {
    //~^ WARNING critical argument `i`
    unsafe { &*i }
}

pub fn just_fine(i: &i32) -> i32 {
    *i
}

fn cast1(p: *const i32) -> i32 {
    let r: &i32 = unsafe { mem::transmute(p) };
    *r
}

#[rustc_error]
fn main() { //~ ERROR: compilation successful
    println!("There are some scary functions in here");
}
