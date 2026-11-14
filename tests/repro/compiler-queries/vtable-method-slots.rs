#![no_std]
#![allow(dead_code)]
pub struct D;
pub struct NoImpl;
pub struct N(*const u8);
pub struct G<T>(T);
pub trait Shape<'a,T> {
    fn explicit(&self);
    fn default_method(&self) {}
    fn send_only(&self) where Self: Send {}
    fn by_value(self);
}
impl<'a> Shape<'a,u8> for D { fn explicit(&self) {} fn by_value(self) {} }
impl<'a> Shape<'a,u8> for N { fn explicit(&self) {} fn by_value(self) {} }
impl<'a,T> Shape<'a,T> for G<T> { fn explicit(&self) {} fn by_value(self) {} }
pub fn query_d(_: &D) {}
pub fn query_n(_: &N) {}
pub fn query_g(_: &G<u8>) {}
pub fn slots_root(d:&D,n:&N,g:&G<u8>,none:&NoImpl) { query_none(none); query_d(d);query_n(n);query_g(g);let _: &dyn Shape<'static,u8>=d;let _: &dyn Shape<'static,u8>=n;let _: &dyn Shape<'static,u8>=g; }

pub fn query_none(_: &NoImpl) {}
