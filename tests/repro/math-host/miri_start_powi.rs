#![no_std]
#![no_main]

// The source argc argument stays a runtime MIR local, so this single `powi`
// call cannot be folded to a literal during MIR construction.
#[unsafe(no_mangle)]
pub fn miri_start(argc: isize, _argv: *const *const u8) -> isize {
    let value = (argc as f32).powi(2);
    value as isize
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
