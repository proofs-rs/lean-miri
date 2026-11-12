#![no_std]

#[repr(C)]
pub struct C { a: u8, b: u64, c: bool }
#[repr(C, packed(2))]
pub struct Packed { a: u8, b: u64, c: bool }
#[repr(align(32))]
pub struct Aligned { a: u16, b: bool, c: [u8; 7] }
#[repr(transparent)]
pub struct Transparent { value: bool, marker: () }
pub struct Reordered { a: u8, b: u64, c: bool, d: [u8; 4] }
pub struct ScalarPair { a: bool, b: u32 }
pub struct Empty;

pub fn aggregate_layouts(x: (C, Packed, Aligned, Transparent, Reordered, ScalarPair, Empty,
    (bool, [u8; 16]), (u32, (bool, u8), u16), ((u8, u8, u8, bool), (u8, bool, u8))))
  -> (C, Packed, Aligned, Transparent, Reordered, ScalarPair, Empty,
    (bool, [u8; 16]), (u32, (bool, u8), u16), ((u8, u8, u8, bool), (u8, bool, u8))) {
    x
}
