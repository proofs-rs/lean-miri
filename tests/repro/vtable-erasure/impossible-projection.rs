#![feature(trivial_bounds)]
#![no_std]
#![no_main]

trait Never {}
trait Pick {
    type Assoc;
}
impl Pick for () {
    type Assoc = for<'named> fn(&'named u8) -> u8;
}
trait Read {
    fn read(&self, value: &u8) -> u8;
}
impl Read for for<'named> fn(&'named u8) -> u8 {
    fn read(&self, value: &u8) -> u8 { self(value) }
}
fn identity(value: &u8) -> u8 { *value }

// This dead function gives the post-analysis normalizer an unrelated
// impossible predicate while retaining a closed HRTB function-pointer cast.
fn dead_projection<'a>() where (): Never {
    let function: <() as Pick>::Assoc = identity;
    let reader: &dyn Read = &function;
    let value = 7;
    let _ = reader.read(&value);
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    0
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
