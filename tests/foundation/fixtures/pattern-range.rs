#![feature(pattern_types, pattern_type_macro)]
#![allow(incomplete_features)]
pub type Small = core::pattern_type!(u8 is 3..=17);
const HIGH_END: usize = isize::MAX as usize;
pub type High = core::pattern_type!(usize is 0..=HIGH_END);
pub type Signed = core::pattern_type!(i8 is -7..=4);
pub type Full = core::pattern_type!(u8 is 0..=255);
pub fn range_input(_small: Small, _high: High, _signed: Signed, _full: Full) {}
