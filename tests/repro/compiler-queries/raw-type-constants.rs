#![no_std]
#![no_main]

#[inline(never)]
fn const_usize<const N: usize>() -> usize { N }
#[inline(never)]
fn const_signed<const N: i16>() -> i16 { N }
#[inline(never)]
fn const_wide<const N: u128>() -> u128 { N }
#[inline(never)]
fn const_bool<const N: bool>() -> bool { N }
#[inline(never)]
fn const_char<const N: char>() -> char { N }

const BYTES: [u8; 3] = [3, 5, 8];
#[inline(never)]
fn residual_bytes() -> [u8; 3] { BYTES }

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    if const_usize::<37>() == 37 && const_signed::<-7>() == -7 &&
        const_wide::<{1_u128 << 100}>() == 1_u128 << 100 && const_bool::<true>() &&
        const_char::<'λ'>() == 'λ' && residual_bytes() == [3, 5, 8] { 0 } else { 1 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
