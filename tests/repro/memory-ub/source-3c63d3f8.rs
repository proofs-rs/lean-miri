#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let pointer = 1usize as *const u32;
    // SAFETY is intentionally violated: address 1 is misaligned for u32.
    let reference = unsafe { &*pointer };
    reference as *const u32 as usize as isize
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
