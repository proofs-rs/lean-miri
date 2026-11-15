#![crate_type = "lib"]
#![no_std]

pub fn safe_pointer(value: fn() -> i32) -> fn() -> i32 { value }
pub fn unsafe_pointer(value: unsafe fn() -> i32) -> unsafe fn() -> i32 { value }
pub fn foreign_pointer(value: extern "C" fn() -> i32) -> extern "C" fn() -> i32 { value }

pub fn scalar_identity(value: u8) -> u8 { value }
