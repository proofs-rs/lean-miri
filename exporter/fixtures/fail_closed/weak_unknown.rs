#![feature(linkage)]
#![no_std]
unsafe extern "C" {
    #[linkage = "extern_weak"]
    static lean_miri_unknown_weak: Option<unsafe extern "C" fn() -> i32>;
}
pub unsafe fn identity() -> i32 {
    match unsafe { lean_miri_unknown_weak } {
        Some(function) => unsafe { function() },
        None => 0,
    }
}
