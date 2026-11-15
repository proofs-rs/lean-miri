#![no_std]
#![feature(lang_items)]
#![allow(internal_features)]

#[lang = "start"]
fn start<T>(_: fn() -> T, argc: isize, _: *const *const u8, _: u8) -> isize {
    main();
    argc
}

fn main() {
    let value: Result<u64, u64> = Ok(5);
    let number = match value { Ok(number) => number, Err(number) => number };
    if number != 5 { loop {} }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
