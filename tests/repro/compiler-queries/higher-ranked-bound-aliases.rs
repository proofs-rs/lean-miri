#![no_std]
#![feature(checked_type_aliases)]
#![allow(dead_code)]
pub struct S;
pub type Identity<T> = T;
pub type CopyIdentity<T: Copy> = T;
pub trait All<X> {}
impl<'a> All<(&'a u8, &'a u8)> for S {}
pub fn plain<T>() where for<'a> T: All<(&'a u8, Identity<&'a u8>)> {}
pub fn checked<T>() where for<'a> T: All<(&'a u8, CopyIdentity<&'a u8>)> {}
pub trait Static<X> {}
impl Static<(&'static u8, &'static u8)> for S {}
pub fn static_only<T>() where for<'a> T: Static<(&'a u8, Identity<&'a u8>)> {}
pub fn capture_static<T: Static<(&'static u8, &'static u8)>>() {}
pub fn higher_ranked_alias_root() { plain::<S>(); checked::<S>(); nested::<S>(); capture_static::<S>(); }
pub trait Every<X> {}
impl<'a, 'b> Every<&'b u8> for &'a u8 {}
pub type Quantified<T: for<'b> Every<&'b u8>> = T;
pub fn nested<T>() where for<'a> T: All<(&'a u8, Quantified<&'a u8>)> {}
