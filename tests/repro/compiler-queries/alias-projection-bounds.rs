#![no_std]
#![feature(checked_type_aliases)]

pub struct Wrapper<T>(pub T);
pub trait Leaf {}
impl Leaf for u8 {}
pub trait Product { type Item; }
impl<T: Leaf> Product for Wrapper<T> { type Item = T; }
// The unused parameter must still satisfy its checked declaration clauses.
pub type ProjectionChecked<T: Product<Item = u8>> = u8;
pub fn checked_projection(value: ProjectionChecked<Wrapper<u8>>) -> u8 { value }
