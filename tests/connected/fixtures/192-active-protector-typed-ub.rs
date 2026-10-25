#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut value = 0u8;
    let parent = core::ptr::addr_of_mut!(value);
    unsafe { protected_write(&mut *parent, parent) };
    0
}

#[inline(never)]
fn protected_write(argument: &mut u8, parent: *mut u8) {
    *argument = 1;
    unsafe { *parent = 2 };
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
