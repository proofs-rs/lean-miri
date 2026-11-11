#![feature(linkage)]
use std::sync::atomic::{AtomicUsize, Ordering};
static DROPS: AtomicUsize = AtomicUsize::new(0);
extern "C" fn destructor(_argument: *mut ()) { DROPS.fetch_add(1, Ordering::SeqCst); }
unsafe extern "C" {
    #[linkage = "extern_weak"]
    static __cxa_thread_atexit_impl: Option<unsafe extern "C" fn(*mut (), *mut (), *mut ()) -> i32>;
    #[linkage = "extern_weak"]
    static __dso_handle: *mut u8;
}
fn main() {
    let function = unsafe { __cxa_thread_atexit_impl }.expect("pinned GNU Miri supplies TLS registration");
    let dso = unsafe { __dso_handle };
    assert!(!dso.is_null());
    assert_eq!(unsafe { function(destructor as *mut (), std::ptr::null_mut(), dso.cast()) }, 0);
    assert_eq!(DROPS.load(Ordering::SeqCst), 0);
}
