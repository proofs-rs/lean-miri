#![no_std]
#![feature(rustc_private)]
extern crate libc;

unsafe extern "C" {
    fn dlsym(handle: *mut libc::c_void, symbol: *const libc::c_char) -> *mut libc::c_void;
}

pub unsafe fn identity() -> *mut libc::c_void {
    unsafe { dlsym(core::ptr::null_mut(), c"getrandom".as_ptr()) }
}
