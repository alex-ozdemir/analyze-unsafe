#![allow(dead_code)]

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
    println!("There are some scary functions in here");
}
