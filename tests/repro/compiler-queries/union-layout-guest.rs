#![no_std]
#![no_main]

union Same { byte: u8, boolean: bool }
union Pair { bytes: (u8, u32), typed: (bool, u32) }
#[repr(C)]
union C { byte: u8, wide: u64 }
#[repr(packed)]
union Packed { first: u32, second: u32 }
union NonZero { restricted: core::num::NonZeroU32, integer: u32 }

#[unsafe(no_mangle)]
pub fn miri_start(argc: isize, _argv: *const *const u8) -> isize {
    let zero = (argc ^ argc) as u32;
    let same = Same { byte: (zero + 1) as u8 };
    if !unsafe { same.boolean } { return 1; }
    let pair = Pair { bytes: ((zero + 1) as u8, zero + 0x12345678) };
    let (boolean, integer) = unsafe { pair.typed };
    if !boolean || integer != 0x12345678 { return 2; }
    let c = C { wide: zero as u64 + 0x1122334455667788 };
    if unsafe { c.byte } != 0x88 { return 3; }
    let packed = Packed { first: zero + 0x87654321 };
    if unsafe { core::ptr::addr_of!(packed.second).read_unaligned() } != 0x87654321 { return 4; }
    let nonzero = NonZero { integer: zero };
    if unsafe { nonzero.integer } != 0 { return 5; }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
