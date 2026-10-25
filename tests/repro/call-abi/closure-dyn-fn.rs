#![no_std]
#![no_main]

// Separate positive fixture: concrete closure -> &dyn Fn -> virtual call.
// The returned zero depends on the dynamically dispatched result.
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let bias = 1u32;
    let closure = |value: u32| value.wrapping_add(bias);
    let callable: &dyn Fn(u32) -> u32 = &closure;
    (callable(8) as isize) - 9
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
