#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let value = 0x1122_3344u32;
    let bytes = &value as *const u32 as *const u8;
    // SAFETY is intentionally violated: this retains the allocation provenance
    // while shifting the pointer by one byte before a typed u32 read.
    unsafe { bytes.add(1).cast::<u32>().read() as isize }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
