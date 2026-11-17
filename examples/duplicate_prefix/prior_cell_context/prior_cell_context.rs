#![no_std]
use core::cell::UnsafeCell;

#[inline(never)]
pub fn prior_context(
    shared: &UnsafeCell<()>,
    bytes: &mut [u8],
) -> (*const UnsafeCell<()>, usize) {
    (shared as *const UnsafeCell<()>, bytes.len())
}
