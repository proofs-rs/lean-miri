#![no_std]
#![no_main]

// Genuine producer/interpreter control; black_box retains typed MIR operations.
#[track_caller]
fn length(bytes: &[u8]) -> usize { core::hint::black_box(bytes).len() }

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut pair = (42u32, true);
    #[cfg(expected_ub)]
    let pointer = core::hint::black_box(&mut pair as *mut (u32, bool));
    let reference = core::hint::black_box(&mut pair);
    reference.0 += 1;
    #[cfg(not(expected_ub))]
    let pointer = core::hint::black_box(reference as *mut (u32, bool));
    let bytes = core::hint::black_box([1u8, 2, 3]);
    let copied = unsafe { *pointer };
    if copied == (43, true) && length(&bytes) == 3 { 0 } else { 1 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
