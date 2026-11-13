#![no_std]
#![allow(dead_code)]
pub struct D;
pub struct NoImpl;
pub struct G<T>(T);
pub trait Shape<T> {
 fn plain(&self);
 fn implementation_track(&self);
 #[track_caller] fn prototype_track(&self);
 #[track_caller] fn default_track(&self) {}
 fn by_value(self);
}
impl Shape<u8> for D {
 fn plain(&self) {}
 #[track_caller] fn implementation_track(&self) {}
 fn prototype_track(&self) {}
 fn by_value(self) {}
}
impl<T> Shape<T> for G<T> {
 fn plain(&self) {}
 #[track_caller] fn implementation_track(&self) {}
 fn prototype_track(&self) {}
 fn by_value(self) {}
}
pub fn query_d(_: &D) {}
pub fn query_g(_: &G<u8>) {}
pub fn query_dyn(_: &dyn Shape<u8>) {}
pub fn instance_root(d:&D,g:&G<u8>,none:&NoImpl) {query_d(d);query_g(g);query_dyn(d);query_none(none);}
pub fn query_none(_: &NoImpl) {}
