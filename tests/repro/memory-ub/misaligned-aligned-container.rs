#![no_std]
#![feature(lang_items)]
#[lang = "start"]
fn start<T>(main: fn() -> T, _argc: isize, _argv: *const *const u8, _sigpipe: u8) -> isize {
    main();
    0
}

#[repr(packed)]
struct Packed { pad: u8, value: u32 }

// The container forces the base to be divisible by four. The packed field
// remains at byte offset one, so its u32 reference is unaligned for every
// permitted allocation address, rather than merely for some random draws.
#[repr(C, align(4))]
struct Storage(Packed);

pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let storage = Storage(Packed { pad: 0, value: 0x1122_3344 });
    let pointer = core::ptr::addr_of!(storage.0.value);
    // SAFETY is intentionally violated: the packed field has offset 1 and
    // does not meet u32's alignment requirement.
    let reference = unsafe { &*pointer };
    reference as *const u32 as usize as isize
}


fn main() { let _ = miri_start(0, core::ptr::null()); }
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
