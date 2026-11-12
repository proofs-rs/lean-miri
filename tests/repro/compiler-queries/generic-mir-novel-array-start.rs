#![no_std]
#![no_main]

#[derive(Clone, Copy)]
struct Novel(u32);

#[inline(never)]
fn local_array<T: Copy>(value: T) -> T {
    let pair = [value, value];
    let _copied = pair;
    value
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    if local_array(Novel(73)).0 == 73 { 0 } else { 1 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
