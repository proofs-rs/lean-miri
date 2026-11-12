#![no_std]
#[inline(never)] pub fn echo<T>(x:T)->T{x}
pub fn instance_names(x:u8)->u8{echo(x)}
