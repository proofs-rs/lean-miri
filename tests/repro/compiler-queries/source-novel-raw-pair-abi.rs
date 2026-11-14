#![no_std]
#[inline(never)] pub fn identity<T>(value:T)->T{value}
pub fn base(x:u8)->u8{identity(x)}
pub fn oracle(x:(*const[u8;5],bool),pointer:fn((*const[u8;5],bool))->(*const[u8;5],bool))
 ->(*const[u8;5],bool){core::hint::black_box(pointer(x));identity(x)}
