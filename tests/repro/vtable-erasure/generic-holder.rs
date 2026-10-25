#![no_std]
#![no_main]
trait Read { fn read(&self) -> u8; }
struct Holder<'value>(&'value u8);
impl<'value> Read for Holder<'value> {
    fn read(&self) -> u8 { *self.0 }
}
fn read_holder<'call>(holder: &'call Holder<'call>) -> u8 {
    let erased: &dyn Read = holder;
    erased.read()
}
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let value = 7;
    let holder = Holder(&value);
    read_holder(&holder) as isize - 7
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
