extern crate libc;

use libc::{c_char, c_int, atoi};

fn main() {
    // Make a string, '256'.
    let really_a_string: [c_char; 4] = [0x32, 0x35, 0x36, 0x00];
    let ptr: *const c_char = &(really_a_string[0]);
    let string_as_int: c_int = unsafe { atoi(ptr) };
    println!("Number: {}", string_as_int);
}
