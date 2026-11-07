#![no_std]
#![feature(lang_items)]

#[inline(never)]
fn sum(n: u32) -> u32 {
    let mut result = 0u32;
    for value in 0..n {
        result = result.wrapping_add(value);
    }
    result
}

fn main() {
    assert!(sum(16) == 120);
}

#[lang = "start"]
fn lang_start<T>(main: fn() -> T, _argc: isize, _argv: *const *const u8, _sigpipe: u8) -> isize {
    main();
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
