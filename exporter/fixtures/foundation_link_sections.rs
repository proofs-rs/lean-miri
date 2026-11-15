#![no_main]
#![no_std]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! { loop {} }
pub fn root(value: u8) -> u8 { value }
#[cfg(selected_section)]
#[used]
#[unsafe(link_section = ".finite_test")]
static USED_SECTION: u8 = 1;
// An extern indicator alone does not imply used: helpers conservatively skips it.
#[unsafe(no_mangle)]
#[unsafe(link_section = ".unused_finite_test")]
pub static UNUSED_SECTION: u8 = 2;
