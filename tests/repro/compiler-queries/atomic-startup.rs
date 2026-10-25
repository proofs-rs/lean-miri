#![no_std]
#![no_main]

use core::sync::atomic::{AtomicU32, Ordering};

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let value = AtomicU32::new(0);
    value.store(4, Ordering::Release);
    let loaded = value.load(Ordering::Acquire);
    let previous = value.fetch_add(3, Ordering::AcqRel);
    let exchanged = value.compare_exchange(7, 9, Ordering::AcqRel, Ordering::Acquire);
    let final_value = value.load(Ordering::SeqCst);

    if loaded == 4 && previous == 4 && exchanged == Ok(7) && final_value == 9 {
        0
    } else {
        1
    }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
