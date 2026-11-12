#![no_std]
#[inline(never)]
pub fn identity<T: Copy>(value: T) -> T { value }
pub fn pointer_base() -> u8 { identity(7_u8) }
pub fn pointer_oracle(value: *const [u8; 13]) -> *const [u8; 13] { identity(value) }
