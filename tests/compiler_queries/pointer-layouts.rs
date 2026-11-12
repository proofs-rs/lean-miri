#![no_std]

pub trait Object { fn value(&self) -> u8; }
pub struct Tail<T: ?Sized> { pub prefix: u32, pub tail: T }

pub fn pointer_layouts(
    a: *mut u32, b: *mut str, c: *mut [u8], d: *mut dyn Object,
    e: &mut u32, f: &mut str, g: &mut [u8], h: &mut dyn Object,
    i: &Tail<[u8]>,
) {
    core::hint::black_box((a, b, c, d, e, f, g, h, i));
}
