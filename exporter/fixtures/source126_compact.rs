#![allow(dead_code)]

pub trait HasValue {
    const VALUE: u32;
}

impl HasValue for u8 {
    const VALUE: u32 = 7;
}

#[inline(never)]
pub fn identity<T: Copy>(value: T) -> T {
    value
}

#[inline(never)]
pub fn associated_value<T: HasValue>() -> u32 {
    T::VALUE
}

#[track_caller]
#[inline(never)]
pub fn tracked<T: Copy>(value: T) -> T {
    let _caller = core::panic::Location::caller();
    value
}

pub fn root(input: u32) -> u32 {
    if input == 0 {
        tracked(identity(associated_value::<u8>()))
    } else {
        tracked(identity(input + associated_value::<u8>()))
    }
}
