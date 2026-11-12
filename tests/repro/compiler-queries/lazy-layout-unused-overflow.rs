#![no_std]
#[unsafe(no_mangle)]
pub fn unused_overflow(x: *const [u8; 2305843009213693952]) -> *const [u8; 2305843009213693952] { x }
