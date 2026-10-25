#![no_std]

extern crate alloc;
use alloc::boxed::Box;

pub trait Marker {
    fn value(&self) -> u8;
}

pub struct Borrowed<'a>(pub &'a u8);

impl Marker for Borrowed<'_> {
    fn value(&self) -> u8 { *self.0 }
}

#[unsafe(no_mangle)]
pub fn borrowed(value: &u8) -> Box<dyn Marker + '_> {
    Box::new(Borrowed(value))
}

#[unsafe(no_mangle)]
pub fn invoke_borrowed(value: &u8) -> u8 {
    borrowed(value).value()
}
