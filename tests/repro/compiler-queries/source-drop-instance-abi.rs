#![no_std]
pub struct Plain(pub [u8;9]);
pub struct Droppy(pub [u8;9]);
impl Drop for Droppy {fn drop(&mut self){}}
#[inline(never)] pub fn consume<T>(_value:T){}
pub fn root(){consume([1u8;9]);consume(Plain([2;9]));consume(Droppy([3;9]));}
