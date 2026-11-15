#![allow(dead_code, unused_variables)]
pub union Mixed { byte: u8, wide: u64 }
pub union Scalar { byte: u8, boolean: bool, empty: () }
pub union Pair { first: &'static str, second: &'static str }
#[repr(C)]
pub union CScalar { first: u64, second: u64 }
#[repr(packed)]
pub union Packed { first: u64, second: u32 }
#[repr(align(16))]
pub union Aligned { first: u64, second: u64 }
pub union Generic<T: Copy> { first: T, second: u16 }
pub fn unions(a: Mixed, b: Scalar, c: Pair, d: CScalar, e: Packed, f: Aligned, g: Generic<u32>) {}
