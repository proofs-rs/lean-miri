#![no_std]

use core::panic::PanicInfo;

static mut TRACE: u32 = 0;

fn append(digit: u32) {
    let trace = core::ptr::addr_of_mut!(TRACE);
    unsafe {
        let current = trace.read();
        trace.write(current * 10 + digit);
    }
}

unsafe extern "C" fn ctor_first() {
    append(1);
}

unsafe extern "C" fn ctor_second() {
    append(2);
}

// Pinned Miri reads a function-pointer array in element order, appends those
// entries to its ctor vector, then calls `pop()` from the vector tail. Thus
// [second, first] executes first then second under this source route; the test
// checks that `miri_start` observes exactly that sequence.
#[used]
#[unsafe(link_section = ".init_array")]
static INIT: [unsafe extern "C" fn(); 2] = [ctor_second, ctor_first];

pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let trace = unsafe { core::ptr::addr_of!(TRACE).read() };
    if trace == 12 { 0 } else { 1 }
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop {
        core::hint::spin_loop();
    }
}
