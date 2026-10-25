#![no_std]
#![no_main]
#![feature(core_intrinsics)]
// Runtime argc prevents the MIR operation from being replaced by a literal.
// sin(1) needs host math; the fixed cos(0) control must not need it.
#[unsafe(no_mangle)]
pub fn miri_start(argc: isize, _argv: *const *const u8) -> isize {
    // Prepared Miri includes the source name in argv; the isolated Lean route
    // has no forwarded arguments. Cancel argc at runtime in both profiles.
    let input = argc as f64;
    let zero = input - input;
    #[cfg(not(fixed_control))]
    let value = core::intrinsics::sin(zero + 1.0);
    #[cfg(fixed_control)]
    let value = core::intrinsics::cos(zero);
    #[cfg(not(fixed_control))]
    let valid = value > 0.84 && value < 0.85;
    #[cfg(fixed_control)]
    let valid = value.to_bits() == 1.0f64.to_bits();
    if valid { 0 } else { 1 }
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
