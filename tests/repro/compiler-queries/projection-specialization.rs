#![no_std]
#![feature(specialization)]
#![allow(incomplete_features)]
pub struct Wrapper<T>(pub T);
pub trait Product { type Item; }
impl<T> Product for Wrapper<T> { default type Item = u8; }
impl Product for Wrapper<u16> { type Item = u16; }
pub fn specialized(value: <Wrapper<u16> as Product>::Item) -> u16 { value }
