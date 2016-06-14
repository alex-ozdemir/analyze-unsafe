#![feature(libc)]
extern crate libc;

use libc::{c_char, c_int, atoi};

unsafe fn echo(i: i64) -> i64 {
    let ptr: *const i64 = &i;
    *ptr
}

fn ohno(i: *const i64) -> i64 {
    unsafe { *i }
}

fn ohno2(i: *const (i64, i64)) -> i64 {
    unsafe { (*i).0 }
}

fn ohno3(i: *const [i64; 5], j: usize) -> i64 {
    unsafe { (*i)[j] }
}

fn ohno4(i: *const [i64; 5]) -> i64 {
    unsafe { (*i)[2] }
}

fn ohno5(i: &i32) -> i32 {
    *i
}

fn main() {
    // Make a string, '256'.
    let really_a_string: [c_char; 4] = [0x32, 0x35, 0x36, 0x00];
    let ptr: *const c_char = &(really_a_string[0]);
    let string_as_int: c_int = unsafe { atoi(ptr) };
    let y = 65;
    println!("Number: {} {}", string_as_int, unsafe { echo(y) } );
}
