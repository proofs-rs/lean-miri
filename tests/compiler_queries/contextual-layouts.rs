#![no_std]
#![feature(pattern_types, pattern_type_macro)]

#[repr(u8)]
pub enum Sparse { A = 3, B = 9 }
#[repr(i8)]
pub enum Signed { A = -5, B = 0, C = 7 }
pub enum Niche { None, Some(core::num::NonZeroU8) }
pub enum OneLive { Never(!), Live(u8) }
pub enum Empty { A(!), B(core::convert::Infallible) }
#[repr(transparent)]
pub struct WrapBool(pub bool);
#[repr(transparent)]
pub struct WrapNonZero(pub core::num::NonZeroU16);
type ByteRange = core::pattern_type!(u8 is 1..=9);
#[repr(transparent)]
pub struct WrapRange(pub ByteRange);
pub union Shared { pub restricted: core::num::NonZeroU32, pub raw: u32 }
pub enum UnionPayload { Unit, Payload(Shared) }
pub enum Mixed { Byte(u8), Wide(u64), Pair(bool, u16) }

pub fn contextual_layouts(x: (Sparse, Signed, Niche, OneLive, Empty, WrapBool,
    WrapNonZero, WrapRange, Shared, UnionPayload, Mixed, u8, i8, u32))
    -> (Sparse, Signed, Niche, OneLive, Empty, WrapBool,
        WrapNonZero, WrapRange, Shared, UnionPayload, Mixed, u8, i8, u32) { x }
