#![no_std]
#![no_main]
#![feature(core_intrinsics)]

// All bases reach powi through runtime MIR locals. Exact bit checks cover the
// C23 fixed exponent-zero result; signaling NaNs are deliberately excluded.
#[unsafe(no_mangle)]
pub fn miri_start(argc: isize, _argv: *const *const u8) -> isize {
    // Prepared Miri supplies argv[0]; the connected miri_start harness has no
    // arguments. Cancel argc so both executions use identical input bits while
    // retaining runtime MIR operands with -Zmir-opt-level=0.
    let runtime_zero = argc ^ argc;
    let finite = runtime_zero + 2;
    let payload = (runtime_zero as u32 & 0x003f_ffff) | 1;
    let bases32 = [
        finite as f32,
        -(finite as f32),
        f32::from_bits(0),
        f32::from_bits(0x8000_0000),
        f32::from_bits(0x7f80_0000),
        f32::from_bits(0xff80_0000),
        f32::from_bits(0x7fc0_0000 | payload),
        f32::from_bits(0xffc0_0000 | payload),
    ];
    for base in bases32 {
        if core::intrinsics::powif32(base, 0).to_bits() != 0x3f80_0000 {
            return 32;
        }
    }
    let payload = (runtime_zero as u64 & 0x0007_ffff_ffff_ffff) | 1;
    let bases64 = [
        finite as f64,
        -(finite as f64),
        f64::from_bits(0),
        f64::from_bits(0x8000_0000_0000_0000),
        f64::from_bits(0x7ff0_0000_0000_0000),
        f64::from_bits(0xfff0_0000_0000_0000),
        f64::from_bits(0x7ff8_0000_0000_0000 | payload),
        f64::from_bits(0xfff8_0000_0000_0000 | payload),
    ];
    for base in bases64 {
        if core::intrinsics::powif64(base, 0).to_bits() != 0x3ff0_0000_0000_0000 {
            return 64;
        }
    }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
