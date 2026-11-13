#![no_std]
#[inline(never)] pub fn identity<T>(x:T)->T{x}
pub fn base(x:u8)->u8{identity(x)}
pub fn oracle(x:[u8;6])->[u8;6]{identity(x)}
