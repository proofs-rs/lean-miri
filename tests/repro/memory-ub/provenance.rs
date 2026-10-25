#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let ptr = core::ptr::without_provenance::<u32>(8);
    // SAFETY is intentionally violated: the non-null aligned address has no
    // allocation provenance and cannot be referenced.
    let reference = unsafe { &*ptr };
    reference as *const u32 as usize as isize
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
