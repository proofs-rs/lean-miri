#![no_std]
#![allow(dead_code)]
pub struct Wrap<T>(pub T);
pub trait Compute<T> {
    fn compute<U>(&self, value:T, extra:U) -> T;
    fn associated<U>(value:T, extra:U) -> T;
}
impl<T:Copy> Compute<T> for Wrap<T> {
    fn compute<U>(&self, _value:T, _extra:U) -> T { self.0 }
    fn associated<U>(value:T, _extra:U) -> T { value }
}
pub fn query_method(value:&Wrap<u8>, x:u8, y:u16)->u8 { value.compute::<u16>(x,y) }
pub fn query_associated(x:u8,y:u16)->u8 { <Wrap<u8> as Compute<u8>>::associated::<u16>(x,y) }
pub fn ordinary_root(x:u8,y:u16)->u8 { query_method(&Wrap(x),x,y)+query_associated(x,y) }
