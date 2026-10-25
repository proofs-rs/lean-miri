#![no_std]
#![no_main]

#[repr(packed)]
struct Packed { pad: u8, value: u32 }

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let packed = Packed { pad: 0, value: 0x1122_3344 };
    let pointer = core::ptr::addr_of!(packed.value);
    // SAFETY is intentionally violated: the packed field has offset 1 and
    // does not meet u32's alignment requirement.
    let reference = unsafe { &*pointer };
    reference as *const u32 as usize as isize
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
