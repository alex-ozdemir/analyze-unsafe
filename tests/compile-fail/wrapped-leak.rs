#![feature(rustc_attrs)]
pub struct MyBox {
    x: i32,
    p: *const i32,
}

impl MyBox {
    pub fn new(i: i32) -> MyBox {
        let mut b = MyBox {
            x: i,
            p: 0 as *const i32,
        };
        b.p = &b.x;
        b
    }
    pub fn get(&self) -> i32 {
        unsafe { *self.p }
    }
    pub fn write(&mut self, p: *const i32) {
        //~^ WARN critical argument `p`
        self.p = p
    }
}

#[rustc_error]
fn main() {} //~ ERROR compilation successful
