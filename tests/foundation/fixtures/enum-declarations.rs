#![allow(dead_code)]
pub enum Choice<T> { Empty, Value(T) }
#[repr(u8)]
pub enum Explicit { First = 7, Second }
pub fn identity(value: Choice<u8>) -> Choice<u8> { value }
pub fn explicit(value: Explicit) -> Explicit { value }
