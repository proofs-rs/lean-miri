#![no_std]
#![allow(dead_code)]

pub union SameScalar { a: bool, b: u8 }
pub union MixedScalar { a: u32, b: f32 }
pub union Pair { a: (u8, u32), b: (bool, u32) }
#[repr(C)]
pub union C { a: bool, b: u8 }
#[repr(packed)]
pub union Packed { a: u32, b: u32 }
#[repr(align(32))]
pub union Aligned { a: u32, b: u32 }
pub union ZeroSized { a: (), b: [u8; 0] }
pub union NonZero { a: core::num::NonZeroU32, b: u32 }

pub fn union_layouts(x: (SameScalar, MixedScalar, Pair, C, Packed, Aligned, ZeroSized, NonZero))
    -> (SameScalar, MixedScalar, Pair, C, Packed, Aligned, ZeroSized, NonZero) { x }
