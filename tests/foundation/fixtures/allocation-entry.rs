#![no_std]
#![feature(lang_items)]
#![allow(internal_features)]
#[lang = "start"]
fn start<T>(_: fn() -> T, argc: isize, _: *const *const u8, _: u8) -> isize {
    let _text = "source-memory";
    argc
}
fn main() {}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
