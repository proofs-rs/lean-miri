#![no_std]
pub trait Leaf {}
pub trait Extra {}
impl Leaf for u8 {}
impl Extra for u16 {}
pub struct Wrapper<T>(pub T);
pub trait Family<T: Leaf> {
    fn method<U: Extra>(value: T, extra: U);
}
impl<T: Leaf> Family<T> for Wrapper<T> {
    fn method<U: Extra>(_value: T, _extra: U) {}
}
pub fn ordinary<T: Leaf, U: Extra>(_value: T, _extra: U) {}
pub fn source_environment_root(value:u8,extra:u16) {
    <Wrapper<u8> as Family<u8>>::method(value,extra);
    ordinary(value,extra);
}
