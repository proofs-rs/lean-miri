#![no_std]
#![feature(arbitrary_self_types, dispatch_from_dyn, unsize)]
use core::marker::Unsize;
use core::ops::{DispatchFromDyn,Receiver};
#[repr(transparent)]
pub struct Wrap<T:?Sized>(*mut T);
impl<T:?Sized> Receiver for Wrap<T> {type Target=T;}
impl<T:?Sized+Unsize<U>,U:?Sized> DispatchFromDyn<Wrap<U>> for Wrap<T> {}
#[repr(transparent)]
pub struct Outer<T:?Sized>(Wrap<T>);
impl<T:?Sized> Receiver for Outer<T> {type Target=T;}
impl<T:?Sized+Unsize<U>,U:?Sized> DispatchFromDyn<Outer<U>> for Outer<T> {}
pub trait Consume {fn consume(self:Outer<Self>,value:u16)->u32;}
pub fn source_receiver(_: &dyn Consume) {}

pub fn source_call(value:Outer<dyn Consume>)->u32 {value.consume(7)}
