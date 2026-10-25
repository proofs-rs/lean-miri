#![no_std]
#![no_main]

use core::ffi::c_void;
use core::sync::atomic::{AtomicU32, Ordering};

extern crate libc;

static X: AtomicU32 = AtomicU32::new(0);
static Y: AtomicU32 = AtomicU32::new(0);
static RESULT_A: AtomicU32 = AtomicU32::new(9);
static RESULT_B: AtomicU32 = AtomicU32::new(9);
static OLD_A: AtomicU32 = AtomicU32::new(9);
static OLD_B: AtomicU32 = AtomicU32::new(9);

extern "C" fn child_a(_arg: *mut c_void) -> *mut c_void {
    let old = X.fetch_add(1, Ordering::Relaxed);
    let _ = unsafe { libc::sched_yield() };
    let observed = Y.load(Ordering::Relaxed);
    OLD_A.store(old, Ordering::Relaxed);
    RESULT_A.store(observed, Ordering::Relaxed);
    core::ptr::null_mut()
}

extern "C" fn child_b(_arg: *mut c_void) -> *mut c_void {
    let old = Y.fetch_add(1, Ordering::Relaxed);
    let _ = unsafe { libc::sched_yield() };
    let observed = X.load(Ordering::Relaxed);
    OLD_B.store(old, Ordering::Relaxed);
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

    if unsafe { libc::pthread_join(thread_a, core::ptr::null_mut()) } != 0 { return 22; }
    if unsafe { libc::pthread_join(thread_b, core::ptr::null_mut()) } != 0 { return 23; }

    let old_a = OLD_A.load(Ordering::Relaxed);
    let old_b = OLD_B.load(Ordering::Relaxed);
    if old_a == 9 || old_b == 9 { return 24; }
    if old_a != 0 { return 30; }
    if old_b != 0 { return 31; }

    let observed_a = RESULT_A.load(Ordering::Relaxed);
    let observed_b = RESULT_B.load(Ordering::Relaxed);
    if observed_a == 9 || observed_b == 9 { return 32; }
    if observed_a > 1 || observed_b > 1 { return 33; }
    if observed_a == 0 && observed_b == 0 { 0 } else { 92 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
