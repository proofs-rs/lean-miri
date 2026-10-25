#![no_std]
#![no_main]

use core::ffi::c_void;
use core::sync::atomic::{AtomicU32, Ordering};

extern crate libc;

static X: AtomicU32 = AtomicU32::new(0);
static Y: AtomicU32 = AtomicU32::new(0);
static RESULT_A: AtomicU32 = AtomicU32::new(9);
static RESULT_B: AtomicU32 = AtomicU32::new(9);

extern "C" fn child_a(_arg: *mut c_void) -> *mut c_void {
    X.store(1, Ordering::SeqCst);
    let observed = Y.load(Ordering::SeqCst);
    RESULT_A.store(observed, Ordering::Relaxed);
    core::ptr::null_mut()
}

extern "C" fn child_b(_arg: *mut c_void) -> *mut c_void {
    Y.store(1, Ordering::SeqCst);
    let observed = X.load(Ordering::SeqCst);
    RESULT_B.store(observed, Ordering::Relaxed);
    core::ptr::null_mut()
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut thread_a: libc::pthread_t = 0;
    let created_a = unsafe {
        libc::pthread_create(&mut thread_a, core::ptr::null(), child_a, core::ptr::null_mut())
    };
    if created_a != 0 { return 20; }

    let mut thread_b: libc::pthread_t = 0;
    let created_b = unsafe {
        libc::pthread_create(&mut thread_b, core::ptr::null(), child_b, core::ptr::null_mut())
    };
    if created_b != 0 { return 21; }

    // Result locations are distinct. Each result is inspected only after both
    // joins have completed, so this reporting path cannot order the litmus loads.
    if unsafe { libc::pthread_join(thread_a, core::ptr::null_mut()) } != 0 { return 22; }
    if unsafe { libc::pthread_join(thread_b, core::ptr::null_mut()) } != 0 { return 23; }
    let observed_a = RESULT_A.load(Ordering::Relaxed);
    let observed_b = RESULT_B.load(Ordering::Relaxed);
    if observed_a == 0 && observed_b == 0 { 90 } else { 0 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
