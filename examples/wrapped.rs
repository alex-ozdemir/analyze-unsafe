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
}

fn main() {
    let b = MyBox::new(5);
    b.get();
}
