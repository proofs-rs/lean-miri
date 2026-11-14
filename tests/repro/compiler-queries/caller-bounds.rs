#![no_std]
pub trait Leaf {}
pub trait Super: Leaf {}
impl Leaf for u8 {}
impl Super for u8 {}
pub struct Positive<T: Super>(pub T);
pub struct Missing<T: ?Sized>(pub *const T);
pub fn caller_bounds_root(value:Positive<u8>,_missing:*const Missing<u32>)->Positive<u8>{value}
