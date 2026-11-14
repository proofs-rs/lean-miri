#![no_std]
#[inline(never)] pub fn identity<T>(x:T)->T{x}
pub fn base(x:u8)->u8{identity(x)}
pub fn oracle(x:[u8;11],pointer:fn([u8;11])->[u8;11])->[u8;11]{
 core::hint::black_box(pointer(x));identity(x)
}
