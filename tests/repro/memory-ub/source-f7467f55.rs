#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let value = core::mem::MaybeUninit::<u32>::uninit();
    // SAFETY is intentionally violated: this reads uninitialized bytes.
    unsafe { value.as_ptr().read() as isize }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
