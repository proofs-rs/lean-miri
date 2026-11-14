#![no_std]
// Small source-only control for NovelMirArray.lean; the executable counterpart
// is generic-mir-novel-array.rs.
#[derive(Clone, Copy)]
pub struct Novel(pub u32);

#[inline(never)]
fn local_array<T: Copy>(value: T) -> T {
    let pair = [value, value];
    let _copied = pair;
    value
}

pub fn root(value: u32) -> u32 { local_array(Novel(value)).0 }
