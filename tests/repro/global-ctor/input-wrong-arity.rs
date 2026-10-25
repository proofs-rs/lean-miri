#![no_std]
#![no_main]

use core::panic::PanicInfo;

static mut CALLBACK_BODY_ENTERED: u32 = 0;

unsafe extern "C" fn wrong_arity_ctor(_argument: u8) {
    unsafe { core::ptr::addr_of_mut!(CALLBACK_BODY_ENTERED).write(1); }
}

// This is a well-typed function-pointer static and a genuine used ELF
// constructor. The callback's one-argument C signature conflicts with Miri's
// source call, which supplies zero arguments.
#[used]
#[unsafe(link_section = ".init_array")]
static INIT: unsafe extern "C" fn(u8) = wrong_arity_ctor;

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let _body_entered = unsafe { core::ptr::addr_of!(CALLBACK_BODY_ENTERED).read() };
    0
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop {
        core::hint::spin_loop();
    }
}
