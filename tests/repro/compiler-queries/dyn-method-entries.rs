#![no_std]
#![feature(dispatch_from_dyn, unsize)]
#![allow(dead_code)]
pub trait IndirectSized: Sized {}
pub struct D;
impl IndirectSized for D {}
pub trait Shape {
    fn object(&self);
    fn super_sized(&self) where Self: IndirectSized;
    fn only_auto(&self) where Self: Send;
    fn outlives(&self) where Self: 'static;
    fn late<'a>(&'a self);
    fn by_value(self);
    fn static_call() where Self: Sized;
    fn generic<T>(&self) where Self: Sized;
    fn return_self(&self) -> Self where Self: Sized;
    fn other_self(&self, other: &Self) where Self: Sized;
}
pub fn bound_capture<T: IndirectSized + Send>() {}
pub fn dispatch_capture<T: core::ops::DispatchFromDyn<U>, U>() {}
pub fn dyn_root(value: &dyn Shape) { bound_capture::<D>(); value.object(); value.late(); dispatch_capture::<&[u8;1], &[u8]>(); }
