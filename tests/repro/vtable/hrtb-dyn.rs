#![no_std]

extern crate alloc;
use alloc::boxed::Box;

pub trait Marker<'a> {
    fn value(&self, input: &'a u8) -> u8;
}

pub struct Hrtb;
impl<'a> Marker<'a> for Hrtb {
    fn value(&self, input: &'a u8) -> u8 { *input }
}

#[unsafe(no_mangle)]
pub fn hrtb_object() -> Box<dyn for<'a> Marker<'a>> {
    Box::new(Hrtb)
}

#[unsafe(no_mangle)]
pub fn invoke_hrtb(input: &u8) -> u8 {
    hrtb_object().value(input)
}
