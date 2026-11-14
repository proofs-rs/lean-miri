#![no_std]
#![feature(unsized_fn_params)]
pub trait Consume { fn consume(self, value: u16) -> u32; }
pub fn source_receiver(_: &dyn Consume) {}
pub fn source_call(value: dyn Consume) -> u32 { value.consume(7) }
