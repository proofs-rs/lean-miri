#![allow(dead_code)]

pub trait Convert {
    fn convert(self) -> u16;
}

impl Convert for u8 {
    fn convert(self) -> u16 { self as u16 }
}

pub fn dispatch<T: Convert>(value: T) -> u16 {
    value.convert()
}

pub fn root() -> u16 { dispatch(7u8) }

pub fn main() { assert!(dispatch(7u8) == 7); }
