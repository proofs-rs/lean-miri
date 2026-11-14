#![no_std]
#![feature(freeze,unsafe_unpin)]
use core::marker::{Freeze,UnsafeUnpin};
pub trait Flagged<T> {
    fn shared(&self,value:T)->T;
    fn mutate(&mut self,value:T)->T;
}
pub fn root(frozen:&(dyn Flagged<u8>+Freeze), unique:&mut(dyn Flagged<u16>+Unpin+UnsafeUnpin)) {
    core::hint::black_box(frozen.shared(7));
    core::hint::black_box(unique.mutate(9));
}
