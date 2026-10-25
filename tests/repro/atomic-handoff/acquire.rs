#![no_std]
#![no_main]

use core::ffi::c_void;
use core::sync::atomic::{AtomicBool, Ordering};

extern crate libc;

static mut SHARED: u32 = 0;
static READY: AtomicBool = AtomicBool::new(false);

extern "C" fn write_then_release(_arg: *mut c_void) -> *mut c_void {
    unsafe { core::ptr::addr_of_mut!(SHARED).write(42); }
    READY.store(true, Ordering::Release);
    core::ptr::null_mut()
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut writer: libc::pthread_t = 0;
    let created = unsafe {
        libc::pthread_create(&mut writer, core::ptr::null(), write_then_release, core::ptr::null_mut())
    };
    if created != 0 { return 1; }

    while !READY.load(Ordering::Acquire) {
        core::hint::spin_loop();
    }
    let observed = unsafe { core::ptr::addr_of!(SHARED).read() };

    // The plain read above is sequenced after the acquire and before the join.
    let joined = unsafe { libc::pthread_join(writer, core::ptr::null_mut()) };
    if joined != 0 { return 2; }
    if observed == 42 { 0 } else { 3 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
