#![no_std]
#![feature(lang_items)]
#![allow(internal_features)]
#[lang = "start"]
fn start<T>(_: fn() -> T, argc: isize, _: *const *const u8, _: u8) -> isize { argc }
fn main() {}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
pub type Padded = (u8, u32, u8);
pub fn large(value: [u64; 3]) -> [u64; 3] { value }
pub fn dense(value: [u8; 4]) -> [u8; 4] { value }
pub fn short(value: [u8; 3]) -> [u8; 3] { value }
pub fn padded(value: Padded) -> Padded { value }
