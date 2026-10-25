#![no_std]
#![no_main]
trait Read<'read> {
    fn read(&self, value: &'read u8) -> u8;
}
impl<'impl_read> Read<'impl_read> for for<'named> fn(&'named u8) -> u8 {
    fn read(&self, value: &'impl_read u8) -> u8 { self(value) }
}
fn identity(value: &u8) -> u8 { *value }
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let function: for<'chosen> fn(&'chosen u8) -> u8 = identity;
    let reader: &dyn for<'call> Read<'call> = &function;
    let value = 7;
    reader.read(&value) as isize - 7
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
