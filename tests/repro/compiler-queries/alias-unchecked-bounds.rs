#![no_std]

pub trait Gate {}
impl Gate for u8 {}

// Ordinary alias bounds are warning-only. u32 intentionally has no Gate impl.
pub type Loose<T: Gate> = T;
pub fn ordinary(value: Loose<u32>) -> u32 { value }
