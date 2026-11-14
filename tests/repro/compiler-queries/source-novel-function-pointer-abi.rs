#![no_std]
pub fn base()->u8 {7}
pub fn oracle(f:for<'a>fn(&'a mut[u8;13])->&'a mut[u8;13],x:&mut[u8;13]) {core::hint::black_box(f(x));}
