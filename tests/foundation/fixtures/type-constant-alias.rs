#![no_std]
pub fn concrete(_: [u8; core::mem::size_of::<u32>()]) {}
pub fn generic<const N: usize>(_: [u8; N]) {}
