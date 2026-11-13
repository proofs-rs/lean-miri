#![no_std]
use core::marker::PhantomData;
#[repr(transparent)] pub struct One<T>(T);
#[repr(align(2))] pub struct AlignTwo;
#[repr(transparent)] pub struct Aligned(AlignTwo);
#[repr(transparent)] pub struct Raw<T:?Sized>(*mut T);
#[repr(transparent)] pub struct Marked<T:?Sized>(*mut T,PhantomData<T>);
#[repr(transparent)] pub struct Borrowed<'a,T:?Sized>(&'a T);
pub trait Consume {fn consume(self,value:u16)->u32;}
pub fn boundary(_:One<()>,_:Aligned,_:Raw<dyn Consume>,_:Marked<dyn Consume>,_:Borrowed<'_,dyn Consume>) {}
