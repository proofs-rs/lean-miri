#![no_std]
#![no_main]

use core::ffi::c_void;
use core::sync::atomic::{AtomicU32, Ordering};

extern crate libc;

static mut SHARED: u32 = 0;
static READY: AtomicU32 = AtomicU32::new(0);

extern "C" fn child_a(_arg: *mut c_void) -> *mut c_void {
    unsafe { core::ptr::addr_of_mut!(SHARED).write(42); }
    READY.store(1, Ordering::Release);
    core::ptr::null_mut()
}

extern "C" fn child_b(_arg: *mut c_void) -> *mut c_void {
    while READY.load(Ordering::Relaxed) < 1 {
        core::hint::spin_loop();
    }

    let old = READY.fetch_add(1, Ordering::Relaxed);
    if old != 1 {
        loop { core::hint::spin_loop(); }
    }
    core::ptr::null_mut()
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut writer_a: libc::pthread_t = 0;
    let created_a = unsafe {
        libc::pthread_create(&mut writer_a, core::ptr::null(), child_a, core::ptr::null_mut())
    };
    if created_a != 0 { return 1; }

    let mut writer_b: libc::pthread_t = 0;
    let created_b = unsafe {
        libc::pthread_create(&mut writer_b, core::ptr::null(), child_b, core::ptr::null_mut())
    };
    if created_b != 0 { return 2; }

    while READY.load(Ordering::Acquire) != 2 {
        core::hint::spin_loop();
    }
    let observed = unsafe { core::ptr::addr_of!(SHARED).read() };

    // Both joins follow the plain read, so neither can synchronize that access.
    let joined_a = unsafe { libc::pthread_join(writer_a, core::ptr::null_mut()) };
    if joined_a != 0 { return 3; }
    let joined_b = unsafe { libc::pthread_join(writer_b, core::ptr::null_mut()) };
    if joined_b != 0 { return 4; }
    if observed == 42 { 0 } else { 5 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
