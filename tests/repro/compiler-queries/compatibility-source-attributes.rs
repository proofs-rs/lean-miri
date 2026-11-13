#![feature(rustc_attrs)]
#![allow(internal_features)]
#[repr(transparent)]
#[rustc_nonnull_optimization_guaranteed]
pub struct Trusted(*const u8);
#[repr(C)]
pub struct Fields { pub first: u16, pub second: u32 }
pub fn source_attributes(_: Trusted, _: Fields) {}
