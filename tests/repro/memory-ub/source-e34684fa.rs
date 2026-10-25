#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let values = [0x1122_3344u32, 0x5566_7788];
    let bytes = values.as_ptr().cast::<u8>();
    // SAFETY is intentionally violated: this retains the allocation provenance
    // while shifting the pointer by one byte before forming a typed reference.
    let reference = unsafe { &*bytes.add(1).cast::<u32>() };
    reference as *const u32 as usize as isize
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
