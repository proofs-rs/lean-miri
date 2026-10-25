#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let dangling: *const u32;
    {
        let value = 0x1122_3344u32;
        dangling = &value;
    }
    // SAFETY is intentionally violated: the stack allocation has ended.
    let reference = unsafe { &*dangling };
    reference as *const u32 as usize as isize
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
