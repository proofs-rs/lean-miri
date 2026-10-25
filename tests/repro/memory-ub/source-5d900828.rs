#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let value = core::mem::MaybeUninit::<u32>::uninit();
    // SAFETY is intentionally violated: this reads uninitialized bytes.
    let pointer = &value as *const core::mem::MaybeUninit<u32> as *const u32;
    unsafe { *pointer as isize }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
