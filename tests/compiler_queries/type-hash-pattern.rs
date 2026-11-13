#![no_std]
#![feature(pattern_types, pattern_type_macro)]

type ByteRange = core::pattern_type!(u8 is 1..=9);
type SignedRange = core::pattern_type!(i8 is -9..=7);
type FullByte = core::pattern_type!(u8 is 0..=255);
type SignedOr = core::pattern_type!(i8 is -128..=-9 | 7..=127);
type ThinNotNull = core::pattern_type!(*const u8 is !null);
type WideNotNull = core::pattern_type!(*const str is !null);

pub struct Anchor;
type NamedNotNull = core::pattern_type!(*const Anchor is !null);

pub fn pattern_layouts(x: (ByteRange, SignedRange, FullByte, SignedOr, ThinNotNull, WideNotNull, NamedNotNull))
    -> (ByteRange, SignedRange, FullByte, SignedOr, ThinNotNull, WideNotNull, NamedNotNull) { x }
