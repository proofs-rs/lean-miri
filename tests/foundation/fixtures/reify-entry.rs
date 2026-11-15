#![no_std]
#![feature(lang_items)]
#![allow(internal_features)]
#[lang = "start"]
fn start<T>(_: fn() -> T, argc: isize, _: *const *const u8, _: u8) -> isize { argc }
fn main() {}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
fn target(value: u8) -> u8 { value }
unsafe fn unsafe_target(value: u8) -> u8 { value }
fn generic_target<T>(value: T) -> T { value }
pub fn safe() -> fn(u8) -> u8 { target }
pub fn unsafe_pointer() -> unsafe fn(u8) -> u8 { unsafe_target }
pub fn generic<T>() -> fn(T) -> T { generic_target::<T> }
