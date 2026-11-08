#![feature(thread_local)]

unsafe extern "C" {
    #[thread_local]
    static EXTERNAL: u32;
}

pub unsafe fn read_external() -> u32 {
    unsafe { EXTERNAL }
}
