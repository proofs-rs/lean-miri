#![no_std]
#![allow(dead_code)]
pub struct S;
pub trait All<X> {}
impl<'a> All<&'a u8> for S {}
pub fn all<T>() where for<'a> T: All<&'a u8> {}
pub trait StaticOnly<X> {}
impl StaticOnly<&'static u8> for S {}
pub fn static_only<T>() where for<'a> T: StaticOnly<&'a u8> {}
pub trait TypeAny<X> {}
impl<X> TypeAny<X> for S {}
pub fn type_any<T>() where for<'a> T: TypeAny<&'a u8> {}
pub trait Repeated<X> {}
impl<'a> Repeated<(&'a u8, &'a u8)> for S {}
pub fn repeated<T>() where for<'a, 'b> T: Repeated<(&'a u8, &'b u8)> {}
pub trait Distinct<X> {}
impl<'a, 'b> Distinct<(&'a u8, &'b u8)> for S {}
pub fn distinct<T>() where for<'a, 'b> T: Distinct<(&'a u8, &'b u8)> {}
pub trait FnFor<X> {}
impl FnFor<for<'a> fn(&'a u8)> for S {}
pub fn fn_for<T>() where T: FnFor<for<'b> fn(&'b u8)> {}
pub trait FnStatic<X> {}
impl FnStatic<fn(&'static u8)> for S {}
pub fn fn_static<T>() where T: FnStatic<for<'a> fn(&'a u8)> {}
pub trait FnGeneralVsStatic<X> {}
impl FnGeneralVsStatic<for<'a> fn(&'a u8)> for S {}
pub fn fn_general_vs_static<T>() where T: FnGeneralVsStatic<fn(&'static u8)> {}

pub fn capture_static<T: StaticOnly<&'static u8>>() {}
pub fn capture_repeated<T: Repeated<(&'static u8, &'static u8)>>() {}
pub fn capture_fn_static<T: FnStatic<fn(&'static u8)>>() {}
pub fn capture_fn_general<T: FnGeneralVsStatic<for<'a> fn(&'a u8)>>() {}
pub fn higher_ranked_root() {
    all::<S>();
    type_any::<S>();
    distinct::<S>();
    fn_for::<S>();
    capture_static::<S>();
    capture_repeated::<S>();
    capture_fn_static::<S>();
    capture_fn_general::<S>();
}
