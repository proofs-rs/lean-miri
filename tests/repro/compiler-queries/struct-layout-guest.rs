#![no_std]
#![no_main]

#[repr(C)]
struct C { small: u8, wide: u64 }
#[repr(packed)]
struct Packed { small: u8, wide: u32 }
#[repr(align(32))]
struct Aligned { small: u8, wide: u64 }
#[repr(transparent)]
struct Transparent(u32);
struct Reordered { small: u8, wide: u64, medium: u16 }

#[unsafe(no_mangle)]
pub fn miri_start(argc: isize, _argv: *const *const u8) -> isize {
    let zero = (argc ^ argc) as u32;
    let c = C { small: (zero + 1) as u8, wide: zero as u64 + 0x1122334455667788 };
    if c.small != 1 || c.wide != 0x1122334455667788 { return 1; }
    let packed = Packed { small: zero as u8, wide: zero + 0x12345678 };
    if unsafe { core::ptr::addr_of!(packed.wide).read_unaligned() } != 0x12345678 { return 2; }
    let aligned = Aligned { small: (zero + 2) as u8, wide: zero as u64 + 33 };
    if aligned.small != 2 || aligned.wide != 33 { return 3; }
    let transparent = Transparent(zero + 7);
    if transparent.0 != 7 { return 4; }
    let reordered = Reordered { small: (zero + 5) as u8, wide: zero as u64 + 66, medium: (zero + 9) as u16 };
    if reordered.small != 5 || reordered.wide != 66 || reordered.medium != 9 { return 5; }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
