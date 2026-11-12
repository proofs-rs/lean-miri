#![no_std]
pub struct Defaults<T=u8,U=T,const N:u8=3>(core::marker::PhantomData<(T,U)>);
pub struct Stop<T=u8,U=u16>(core::marker::PhantomData<(T,U)>);
pub type AllDefaults = Defaults;
pub type Dependent = Defaults<u32>;
pub type KeepEarlier = Defaults<u8,u16,4>;
pub type ElideOnlyTrailing = Defaults<u16,u8>;
pub type StopAtLastMismatch = Stop<u8,u32>;
pub fn default_names(_:Defaults<u16>, _:Stop<u16>) {}
