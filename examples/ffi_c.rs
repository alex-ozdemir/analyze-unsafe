#![feature(libc)]
extern crate libc;

use libc::{c_char, c_int, atoi};

unsafe fn echo(i: i64) -> i64 {
    let ptr: *const i64 = &i;
    *ptr
}

fn main() {
    // Make a string, '256'.
    let really_a_string: [c_char; 4] = [0x32, 0x35, 0x36, 0x00];
    let ptr: *const c_char = &(really_a_string[0]);
    let string_as_int: c_int = unsafe { atoi(ptr) };
    let y = 65;
    println!("Number: {} {}", string_as_int, unsafe { echo(y) } );
}
