#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub static FOREIGN_STATIC_TARGET: u32 = 29;

unsafe extern "C" {
    #[link_name = "FOREIGN_STATIC_TARGET"]
    static FOREIGN_STATIC_DECL: u32;
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    unsafe { let _ = core::ptr::addr_of!(FOREIGN_STATIC_DECL).read(); }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
