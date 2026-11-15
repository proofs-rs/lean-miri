#![no_std]
pub union Bits { pub byte: u8, pub word: u32 }
pub fn byte(value: u8) -> Bits { Bits { byte: value } }
pub fn word(value: u32) -> Bits { Bits { word: value } }
pub union Storage<T: Copy> { pub value: T, pub raw: u64 }
pub fn generic<T: Copy>(value: T) -> Storage<T> { Storage { value } }
pub struct Pair { pub a: u8, pub b: u32 }
pub fn pair(a: u8, b: u32) -> Pair { Pair { a, b } }
