#![no_std]
#![feature(auto_traits)]
#![allow(dead_code)]

pub struct Wrapper<T>(pub T);
pub trait Leaf {}
impl Leaf for u8 {}
impl Leaf for u16 {}
pub auto trait Gate {}
impl<T: Leaf> Gate for Wrapper<T> {}
// Statically unreachable constructor: its concrete impl is outside the source
// constructor domain; querying it must report Unsupported, never noSolution.
pub struct Outside;
impl Gate for Outside {}
pub trait Product { type Item; }
impl<T: Leaf> Product for Wrapper<T> { type Item = T; }
pub type Good = Wrapper<u8>;
pub type Bad = Wrapper<u32>;
// The exporter never encounters this concrete ADT instantiation in MIR.
pub type Novel = Wrapper<u16>;

#[inline(never)]
pub fn trait_program_root(value: Good) -> <Good as Product>::Item { value.0 }
