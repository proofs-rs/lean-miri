#![no_std]
fn value(x: u8) -> u8 { x }
unsafe fn unsafe_value(x: u8) -> u8 { x }
pub fn safe() -> fn(u8) -> u8 { value }
pub fn unsafe_pointer() -> unsafe fn(u8) -> u8 { unsafe_value }
pub fn explicit() -> fn(u8) -> u8 { value as fn(u8) -> u8 }
fn identity<T>(value: T) -> T { value }
pub fn generic<T>() -> fn(T) -> T { identity::<T> }
