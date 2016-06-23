#![allow(dead_code)]

pub fn use_offset(p: *const i32) -> *const i32 {
    unsafe { p.offset(1) }
}

pub fn use_as_ref<'a>(p: *const i32) -> Option<&'a i32> {
    unsafe { p.as_ref() }
}

pub fn use_as_mut<'a>(p: *mut i32) -> Option<&'a mut i32> {
    unsafe { p.as_mut() }
}

fn main() { }
