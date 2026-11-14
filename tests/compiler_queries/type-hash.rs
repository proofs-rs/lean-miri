#![no_std]
#![feature(f16, f128)]
pub fn type_hashes(x: (bool, char, i8, i16, i32, i64, i128, isize,
    u8, u16, u32, u64, u128, usize, f16, f32, f64, f128,
    *const u8, *mut (), *const [u16], ((u32, bool), *mut str, *const [u16]))) {
    core::hint::black_box(x);
}
