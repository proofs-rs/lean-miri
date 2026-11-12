#![no_std]
#![feature(never_type)]

pub fn sequence_layouts(x: ([u8; 0], [u16; 3], [(); 9], [!; 0], [!; 1], [core::num::NonZeroU8; 2]),
    _bytes: &[u32], _flags: &[bool], _text: &str)
    -> ([u8; 0], [u16; 3], [(); 9], [!; 0], [!; 1], [core::num::NonZeroU8; 2]) { x }
