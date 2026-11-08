#![feature(pattern_types, pattern_type_macro)]

pub fn add_one(value: u32) -> u32 { value + 1 }

#[repr(C)]
pub struct FloatPair(pub f32, pub f32);

// The target C ABI exercises cast targets, registers and argument attributes.
pub extern "C" fn copy_pair(value: FloatPair) -> FloatPair { value }

pub trait Value { fn value(&self) -> u32; }
pub struct Concrete;
impl Value for Concrete { fn value(&self) -> u32 { 17 } }
pub static VTABLE_ROOT: &(dyn Value + Sync) = &Concrete;
pub fn vtable_root() -> &'static (dyn Value + Sync) { VTABLE_ROOT }

pub fn preserve_lifetime<'a>(value: &'a u32) -> &'a u32 { value }

pub type Positive = std::pat::pattern_type!(u32 is 1..=u32::MAX);
pub fn preserve_pattern(value: Positive) -> Positive { value }
pub type Sparse = std::pat::pattern_type!(i32 is i32::MIN..=-1 | 1..=i32::MAX);
pub fn preserve_or_pattern(value: Sparse) -> Sparse { value }
