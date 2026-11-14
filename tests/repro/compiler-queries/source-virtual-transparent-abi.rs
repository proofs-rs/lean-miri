#![no_std]
#![feature(arbitrary_self_types, dispatch_from_dyn, unsize)]
use core::marker::Unsize;
use core::ops::{DispatchFromDyn,Receiver};
#[repr(transparent)]
pub struct Wrap<T:?Sized>(*mut T);
impl<T:?Sized> Receiver for Wrap<T> {type Target=T;}
impl<T:?Sized+Unsize<U>,U:?Sized> DispatchFromDyn<Wrap<U>> for Wrap<T> {}
pub trait Consume {fn consume(self:Wrap<Self>,value:u16)->u32;}
pub fn source_receiver(_: &dyn Consume) {}

pub fn source_call(value:Wrap<dyn Consume>)->u32 {value.consume(7)}
