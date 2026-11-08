#![no_std]

unsafe extern "C" {
    fn memcmp(left: *const u8, right: *const u8, count: usize) -> i32;
}

pub unsafe fn identity(value: u32) -> u32 {
    let pointer = &value as *const u32 as *const u8;
    let _ = unsafe { memcmp(pointer, pointer, 0) };
    value
}
