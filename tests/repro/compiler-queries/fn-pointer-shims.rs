#![feature(fn_static)]
#![no_std]
use core::ops::FnPtr;
pub type Plain = fn(u32) -> u64;
pub type Unsafe = unsafe fn(u8) -> u16;
pub type Foreign = extern "C" fn(u32, usize) -> u32;
pub type Variadic = unsafe extern "C" fn(u32, ...) -> u32;
pub fn roundtrip(pointer: Plain) -> Plain {
    unsafe { Plain::from_ptr(pointer.as_ptr()) }
}
