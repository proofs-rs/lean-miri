#![no_std]
#![no_main]
static STATIC_VALUE: u32 = 41;
#[inline(never)]
fn target_function() {}
unsafe extern "Rust" {
    fn miri_get_alloc_id(ptr: *const ()) -> u64;
}
#[unsafe(no_mangle)]
pub fn miri_start(argc: isize, argv: *const *const u8) -> isize {
    if argc != 2 { return 90; }
    let local_value = 17u32;
    let selector = unsafe { *argv.add(1) };
    let tag = unsafe { *selector };
    let pointer = match tag {
        b'l' => (&local_value as *const u32).cast::<()>(),
        b's' => (&STATIC_VALUE as *const u32).cast::<()>(),
        b'f' => target_function as *const (),
        _ => return 91,
    };
    unsafe { miri_get_alloc_id(pointer) as isize }
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
