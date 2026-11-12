#![no_std]
#![allow(dead_code)]

pub struct Plain(pub u8);
pub struct Conditional<T>(pub T);
impl<T: Copy> Copy for Conditional<T> {}
impl<T: Copy> Clone for Conditional<T> { fn clone(&self) -> Self { *self } }

#[inline(never)]
pub fn source_function<T>(value: T) -> T { value }
pub fn pointer_signature(value: u16) -> u8 { value as u8 }

pub fn copy_clone_root(value: Conditional<u8>, plain: Plain) -> (Conditional<u8>, Plain, u8) {
    (value, plain, source_function(1u8))
}
