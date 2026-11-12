#![no_std]
#![no_main]

#[inline(never)]
fn leaf<T: Copy>(value: T) -> T { value }

#[inline(never)]
fn relay<T: Copy>(value: T) -> T { leaf(value) }

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    if relay(73_u32) == 73 && relay(19_u64) == 19 { 0 } else { 1 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
