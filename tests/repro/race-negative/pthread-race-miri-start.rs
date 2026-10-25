#![no_std]
#![no_main]

use core::ffi::c_void;

extern crate libc;

static mut SHARED: u32 = 0;

extern "C" fn read_shared(arg: *mut c_void) -> *mut c_void {
    unsafe { let _ = core::ptr::read_volatile(arg.cast::<u32>()); }
    core::ptr::null_mut()
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let shared = core::ptr::addr_of_mut!(SHARED).cast::<c_void>();
    let mut reader: libc::pthread_t = 0;
    let created = unsafe {
        libc::pthread_create(&mut reader, core::ptr::null(), read_shared, shared)
    };
    if created != 0 { return 1; }

    // This main-thread write conflicts with the child's volatile read. Joining
    // happens afterward, so it cannot order the two accesses before the race.
    unsafe { core::ptr::write_volatile(shared.cast::<u32>(), 1); }
    let joined = unsafe { libc::pthread_join(reader, core::ptr::null_mut()) };
    if joined != 0 { return 2; }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
