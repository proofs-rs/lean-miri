#![no_std]
#![feature(checked_type_aliases)]
#![allow(dead_code)]
pub struct S;
pub trait Bound {}
impl Bound for u8 {}
pub type Byte = u8;
pub type Wide = u16;
pub type Checked<T: Bound> = T;
pub trait Every<X> {}
impl<'a> Every<&'a u8> for u8 {}
pub type Quantified<T: for<'b> Every<&'b u8>> = T;
pub trait All<X> {}
impl<'a> All<(&'a u8, u8)> for S {}
pub fn plain<T>() where for<'a> T: All<(&'a u8, Byte)> {}
pub fn checked<T>() where for<'a> T: All<(&'a u8, Checked<u8>)> {}
pub fn quantified_checked<T>() where for<'a> T: All<(&'a u8, Quantified<u8>)> {}
pub fn wrong<T>() where for<'a> T: All<(&'a u8, Wide)> {}
pub trait FnAll<X> {}
impl FnAll<for<'a> fn(&'a u8, u8)> for S {}
pub fn nested<T>() where T: FnAll<for<'a> fn(&'a u8, Byte)> {}
pub fn nested_checked<T>() where T: FnAll<for<'a> fn(&'a u8, Checked<u8>)> {}
pub trait Static<X> {}
impl Static<(&'static u8, u8)> for S {}
pub fn static_only<T>() where for<'a> T: Static<(&'a u8, Checked<u8>)> {}
pub fn capture_static<T: Static<(&'static u8, u8)>>() {}
pub fn capture_wide(value: Wide) -> Wide { value }
pub fn higher_ranked_alias_root() {
    plain::<S>(); checked::<S>(); quantified_checked::<S>(); nested::<S>(); nested_checked::<S>();
    capture_static::<S>(); let _ = capture_wide(17);
}
