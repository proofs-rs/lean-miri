#![no_std]
pub struct Wrapper<T>(pub T);
pub trait Leaf {}
impl Leaf for u8 {}
impl Leaf for u16 {}
pub trait Product {
    type Item<U> where U: Leaf;
}
impl<T: Leaf> Product for Wrapper<T> {
    type Item<U> = U where U: Leaf;
}
pub fn gat(value: <Wrapper<u8> as Product>::Item<u16>) -> u16 { value }

#[cfg(reject_bound)]
pub fn rejected(value: <Wrapper<u8> as Product>::Item<u32>) -> u32 { value }
