#![no_std]
#![no_main]
trait Read { fn read(&self, value: &u8) -> u8; }
impl<F> Read for F where F: for<'named> Fn(&'named u8) -> u8 {
    fn read(&self, value: &u8) -> u8 { self(value) }
}
fn identity(value: &u8) -> u8 { *value }
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let reader: &dyn Read = &identity;
    let value = 7;
    reader.read(&value) as isize - 7
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
