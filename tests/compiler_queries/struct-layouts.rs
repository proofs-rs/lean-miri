#![no_std]
use core::cell::UnsafeCell;
use core::num::NonZeroU32;

pub fn struct_layouts(
    a: UnsafeCell<bool>, b: UnsafeCell<(bool, NonZeroU32)>,
    c: UnsafeCell<[bool; 2]>, d: UnsafeCell<()>, e: *mut UnsafeCell<[bool]>,
) -> (UnsafeCell<bool>, UnsafeCell<(bool, NonZeroU32)>,
      UnsafeCell<[bool; 2]>, UnsafeCell<()>, *mut UnsafeCell<[bool]>) {
    (a, b, c, d, e)
}
