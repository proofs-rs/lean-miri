#![no_std]
#![no_main]
// Use -Zmir-opt-level=0 to retain the tuple and uninitialized ADT local.
#[derive(Clone, Copy)]
struct Novel(u32);
struct Wrapper<T>(T);

#[inline(never)]
fn local_types<T: Copy>(value: T) -> T {
    let pair = (value, value);
    let _copied = pair;
    let _reserved: Wrapper<T>;
    value
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    if local_types(Novel(73)).0 == 73 { 0 } else { 1 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
