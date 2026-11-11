#![feature(linkage)]
unsafe extern "C" {
    #[linkage = "extern_weak"]
    static getrandom: Option<unsafe extern "C" fn(*mut u8, usize, u32) -> isize>;
}
pub unsafe fn identity(buffer: *mut u8, len: usize) -> isize {
    match unsafe { getrandom } {
        Some(function) => unsafe { function(buffer, len, 0) },
        None => -1,
    }
}
