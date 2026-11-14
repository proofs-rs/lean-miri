#![no_std]
pub trait Generic<T>{fn call(&self,value:T)->T;}
pub fn base(x:&dyn Generic<u8>){core::hint::black_box(x.call(1));}
pub fn oracle(x:&dyn Generic<[u8;5]>){core::hint::black_box(x.call([0;5]));}
