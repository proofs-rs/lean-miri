#![no_std]
#![no_main]

// The argc argument stays a runtime MIR local. Two external powi shim calls
// expose both selected outer choices to the same live source execution.
unsafe extern "C" {
    #[link_name = "powif32"]
    fn source_powi(base: f32, exponent: i32) -> f32;
}

#[unsafe(no_mangle)]
pub fn miri_start(argc: isize, _argv: *const *const u8) -> isize {
    let first = unsafe { source_powi(argc as f32, 2) };
    let second = unsafe { source_powi((argc + 1) as f32, 2) };
    (first + second) as isize
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
