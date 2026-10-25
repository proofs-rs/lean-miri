#![allow(dead_code)]

pub unsafe fn assembly_identity(mut value: u64) -> u64 {
    unsafe {
        core::arch::asm!("/* {0} */", inout(reg) value,
            options(nomem, nostack, preserves_flags));
    }
    value
}

pub fn repeat_and_borrow(value: u32) -> u32 {
    let array = [value; 3];
    let shared = &array;
    shared[1]
}

pub fn raw_pointer(value: &mut u32) -> *mut u32 {
    &raw mut *value
}
