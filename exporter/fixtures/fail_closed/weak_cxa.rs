#![feature(linkage)]
unsafe extern "C" {
    #[linkage = "extern_weak"]
    static __cxa_thread_atexit_impl: Option<unsafe extern "C" fn(*mut (), *mut (), *mut ()) -> i32>;
}
pub unsafe fn identity(arg: *mut ()) -> i32 {
    match unsafe { __cxa_thread_atexit_impl } {
        Some(function) => unsafe { function(arg, arg, arg) },
        None => -1,
    }
}
