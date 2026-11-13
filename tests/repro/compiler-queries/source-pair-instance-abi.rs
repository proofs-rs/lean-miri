#![no_std]
#[inline(never)]
pub fn identity<T>(value:T)->T {value}
#[inline(never)]
pub fn residual(value:(*const u8,u64))->(*const u8,u64) {value}
pub fn root() {
 core::hint::black_box(identity((true,false)));
 core::hint::black_box(identity((1u8,2u64)));
 core::hint::black_box(identity((1u64,2u8)));
 core::hint::black_box(identity((1i16,2i32)));
 core::hint::black_box(identity((1u64,2u64)));
 core::hint::black_box(identity((1f32,2f64)));
 core::hint::black_box(identity(('a',true)));
 core::hint::black_box(identity((1usize,2isize)));
 core::hint::black_box(residual((core::ptr::null(),1)));
}
