#![no_std]
#[derive(Clone, Copy)]
pub struct Novel(pub u32);
pub struct Wrapper<T>(pub T);

#[inline(never)]
fn local_types<T: Copy>(value: T) -> T {
    let pair = (value, value);
    let _copied = pair;
    let _reserved: Wrapper<T>;
    value
}

pub fn root(value: u32) -> u32 { local_types(Novel(value)).0 }
