#![no_std]
#![feature(checked_type_aliases)]

pub trait Gate {}
impl Gate for u8 {}
pub type Checked<T: Gate> = T;
pub fn checked(value: Checked<u8>) -> u8 { value }

#[cfg(reject_bound)]
pub fn rejected(value: Checked<u32>) -> u32 { value }
