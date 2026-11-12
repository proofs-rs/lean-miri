#![no_std]
#[inline(never)]
pub fn identity<T>(value: T) -> T { value }
pub fn reference_base() -> u8 { identity(7_u8) }
pub fn reference_oracle(value: &mut [u8; 13]) -> &mut [u8; 13] { identity(value) }
