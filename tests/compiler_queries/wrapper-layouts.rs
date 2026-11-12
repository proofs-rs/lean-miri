#![no_std]

pub trait SizedSuper: Sized {}
impl<T> SizedSuper for T {}

pub struct SizedWrapper<T> { pub prefix: u8, pub stamp: u32, pub value: T }
pub struct InheritedWrapper<T: ?Sized + SizedSuper> { pub prefix: u8, pub stamp: u32, pub value: T }
pub struct MaybeWrapper<T: ?Sized> { pub prefix: u8, pub stamp: u32, pub value: T }
pub struct Novel { pub small: u16, pub byte: u8, pub restricted: bool }

pub fn wrapper_material(x: (SizedWrapper<u8>, InheritedWrapper<u8>, MaybeWrapper<u8>, Novel))
    -> (SizedWrapper<u8>, InheritedWrapper<u8>, MaybeWrapper<u8>, Novel) { x }

pub fn wrapper_oracle(x: (SizedWrapper<Novel>, InheritedWrapper<Novel>, MaybeWrapper<Novel>))
    -> (SizedWrapper<Novel>, InheritedWrapper<Novel>, MaybeWrapper<Novel>) { x }
