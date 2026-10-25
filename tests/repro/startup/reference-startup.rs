#![no_std]
#![no_main]

// The pinned Miri no_std entry ABI. The nonzero result exercises the
// reference sidecar's completed-guest-versus-evaluation-error distinction.
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    7
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
