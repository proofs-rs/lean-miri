#![no_std]
#![no_main]

// These pointer types require complete array layouts, but no guest allocation
// or array traversal. Exporting their offsets must not allocate 1 PiB vectors.
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let bytes = core::ptr::without_provenance::<[u8; 1 << 50]>(16);
    let words = core::ptr::without_provenance::<[u32; 1 << 48]>(32);
    let zero_sized = core::ptr::without_provenance::<[(); usize::MAX]>(48);
    if bytes.cast::<u8>().addr() != 16 || words.cast::<u8>().addr() != 32 ||
        zero_sized.cast::<u8>().addr() != 48 { 1 } else { 0 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
