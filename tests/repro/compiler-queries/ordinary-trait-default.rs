#![no_std]
#![allow(dead_code)]
#[derive(Copy,Clone)]
pub struct Wrap<T>(pub T);
pub trait Compute<T:Copy>:Copy {
    fn compute<U:Copy>(self, value:T, _extra:U) -> T where Self:Sized { value }
    fn associated<U:Copy>(value:T, _extra:U) -> T { value }
}
impl<T:Copy> Compute<T> for Wrap<T> {}
pub fn query_method(x:u8, y:u16)->u8 { Wrap(x).compute::<u16>(x,y) }
pub fn query_associated(x:u8,y:u16)->u8 { <Wrap<u8> as Compute<u8>>::associated::<u16>(x,y) }
pub fn ordinary_root(x:u8,y:u16)->u8 { query_method(x,y)+query_associated(x,y) }
