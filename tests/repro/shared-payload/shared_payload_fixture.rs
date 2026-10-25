#![no_std]

#[inline(never)]
fn identity<T: Copy>(value: T) -> T {
    value
}

#[track_caller]
#[inline(never)]
pub fn tracked_sum(value: u32) -> u32 {
    let line = core::panic::Location::caller().line();
    identity(value).wrapping_add(line)
}

#[inline(never)]
pub fn root(value: u32) -> u32 {
    let array = [value, value.wrapping_add(1), value.wrapping_add(2)];
    let pair = (array[0], array[1]);
    let other = identity(pair);
    tracked_sum(other.0.wrapping_add(other.1).wrapping_add(array[2]))
}
