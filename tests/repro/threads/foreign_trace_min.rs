#![no_std]

unsafe extern "C" {
    fn memcpy(dst: *mut u8, src: *const u8, len: usize) -> *mut u8;
}

#[no_mangle]
pub unsafe extern "C" fn entry(dst: *mut u8, src: *const u8, len: usize) -> *mut u8 {
    unsafe { memcpy(dst, src, len) }
}
