#![no_std]
#![feature(lang_items, sized_type_properties)]
#![allow(internal_features)]
#[lang = "start"]
fn start<T>(_: fn() -> T, argc: isize, _: *const *const u8, _: u8) -> isize {
    main();
    argc
}
fn main() {
    let size = <u64 as core::mem::SizedTypeProperties>::SIZE;
    if size != 8 { loop {} }
}
pub fn unused<T>() -> usize { <T as core::mem::SizedTypeProperties>::SIZE }
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
