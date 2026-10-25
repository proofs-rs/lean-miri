#![no_std]
#![no_main]

use core::ffi::c_void;
use core::sync::atomic::{AtomicU32, Ordering};

extern crate libc;

static mut SHARED: u32 = 0;
static READY: AtomicU32 = AtomicU32::new(0);

extern "C" fn write_then_release(_arg: *mut c_void) -> *mut c_void {
    unsafe { core::ptr::addr_of_mut!(SHARED).write(42); }
    READY.store(1, Ordering::Release);
    core::ptr::null_mut()
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut writer: libc::pthread_t = 0;
    let created = unsafe {
        libc::pthread_create(&mut writer, core::ptr::null(), write_then_release, core::ptr::null_mut())
    };
    if created != 0 { return 1; }

    while READY.load(Ordering::Relaxed) != 1 {
        core::hint::spin_loop();
    }
    let failed_value = match READY.compare_exchange(0, 2, Ordering::Acquire, Ordering::Acquire) {
        Ok(_) => return 4,
        Err(value) => value,
    };
    let observed = unsafe { core::ptr::addr_of!(SHARED).read() };

    // This read is sequenced after the failed acquire CAS and before pthread_join.
    let joined = unsafe { libc::pthread_join(writer, core::ptr::null_mut()) };
    if joined != 0 { return 2; }
    if failed_value == 1 && observed == 42 { 0 } else { 3 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
