fn meh1(p: *const i32) -> i32 {
    unsafe { *(p.offset(1)) }
}

pub fn bad1(p: *const i32, q: *const i32) -> i32 {
    meh1(p) + meh1(q)
}

mod unsafe_stuff {
    pub fn meh2(p: *const i32) -> i32 {
        unsafe { *p }
    }

    // Not problematic on its own, but because it is re-exported it is problematic
    pub fn bad3(p: *const i32) -> i32 {
        meh2(p)
    }
}

pub use unsafe_stuff::bad3;

pub fn bad2(p: *const i32) -> i32 {
    unsafe_stuff::meh2(p)
}

pub unsafe fn ok1(p: *const i32) -> i32 {
    *p
}

#[allow(unused_variables)]
pub fn produce(p: *const i32) -> i32 {
    0
}

pub fn ok2(p: *const i32) -> i32 {
    produce(p)
}

//pub fn ok3(r: &i32) -> i32 {
//    let p: *const _ = r;
//    unsafe { *p }
//}

fn main() {}
