#![no_std]
#![feature(sized_type_properties)]
#[unsafe(no_mangle)]
pub fn probe() -> usize { <u64 as core::mem::SizedTypeProperties>::SIZE }
