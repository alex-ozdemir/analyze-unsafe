#![allow(dead_code)]

fn fn_a(i: i32) -> i32 {
    fn_b(i)
}

fn fn_b(i: i32) -> i32 {
    i + 1
}

fn main() { println!("hi"); }
