#![feature(rustc_attrs)]
#![allow(dead_code)]

#[rustc_error]
fn main(){ } //~ERROR compilation successful

pub enum MyEnum {
    A(*const i32),
    B(*const i32),
}

pub fn ok(p: *const i32) -> i32 {
    let e = MyEnum::A(p);
    match e {
        MyEnum::A(_) => 0,
        MyEnum::B(p) => unsafe { *p },
    }
}
