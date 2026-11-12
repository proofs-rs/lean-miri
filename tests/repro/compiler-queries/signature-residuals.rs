#![no_std]
#[inline(never)]
pub fn borrowed(value: &u32) -> &u32 { value }
#[repr(transparent)]
pub struct Wrapper(u32);
#[inline(never)]
pub fn aggregate(value: Wrapper) -> Wrapper { value }
#[inline(never)]
pub fn root() -> u32 {
    let value = 7;
    *borrowed(&value) + aggregate(Wrapper(8)).0
}
