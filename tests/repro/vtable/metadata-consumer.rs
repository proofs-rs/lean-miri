#![no_std]
#![no_main]
// No local concrete-to-dyn coercion: use the external constant's decoded vtable.
// This is an identity control, not a nonidentity erase/anonymize witness.
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    vtable_metadata_producer::OBJECT.value(&9) as isize - 9
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
