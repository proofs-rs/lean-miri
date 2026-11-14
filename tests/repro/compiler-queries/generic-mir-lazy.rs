#![no_std]

#[inline(never)]
fn identity<T: Copy>(value: T) -> T { value }

pub fn root(value: u32) -> u32 { identity(value) }
