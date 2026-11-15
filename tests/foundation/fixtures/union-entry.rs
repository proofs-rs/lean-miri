#![no_std]
#![feature(lang_items)]
#![allow(internal_features)]
#[lang = "start"]
fn start<T>(_: fn() -> T, argc: isize, _: *const *const u8, _: u8) -> isize { argc }
fn main() {}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
pub union Bits { pub byte: u8, pub word: u32 }
pub fn byte(value: u8) { let _storage = Bits { byte: value }; }
pub fn word(value: u32) { let _storage = Bits { word: value }; }
pub union Storage<T: Copy> { pub value: T, pub raw: u64 }
pub fn generic<T: Copy>(value: T) { let _storage = Storage { value }; }
