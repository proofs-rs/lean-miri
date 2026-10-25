#![no_std]

pub static BYTES: &[u8; 3] = b"abc";

pub fn first() -> u8 {
    BYTES[0]
}
