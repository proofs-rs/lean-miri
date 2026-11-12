#![no_std]
pub type Safe = fn(bool) -> u8;
pub type Unsafe = unsafe fn(i32, *mut u8);
pub type C = extern "C" fn(*const u8) -> bool;
pub type CUnwind = unsafe extern "C-unwind" fn() -> i32;
pub type Variadic = unsafe extern "C" fn(i32, ...) -> i32;
pub type Nested = fn(fn(u8) -> bool) -> fn();
