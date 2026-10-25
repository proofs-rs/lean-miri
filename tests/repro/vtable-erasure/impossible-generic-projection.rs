#![feature(trivial_bounds)]
#![no_std]
#![no_main]

struct Foo;
trait Pick<'a> { type Assoc; }
impl Pick<'static> for Foo {
    type Assoc = for<'named> fn(&'named u8) -> u8;
}
trait Read { fn read(&self, value: &u8) -> u8; }
impl Read for for<'named> fn(&'named u8) -> u8 {
    fn read(&self, value: &u8) -> u8 { self(value) }
}
struct Wrap<'a>
where Foo: Pick<'a>,
{
    pointer: for<'named> fn(&'named u8) -> u8,
    associated: <Foo as Pick<'a>>::Assoc,
}
impl<'a> Read for Wrap<'a>
where Foo: Pick<'a>, <Foo as Pick<'a>>::Assoc: Read,
{
    fn read(&self, value: &u8) -> u8 { (self.pointer)(value) }
}
fn identity(value: &u8) -> u8 { *value }
trait Never {}
fn dead_projection<'a, T>(wrap: Wrap<'a>)
where Foo: Pick<'a>, <Foo as Pick<'a>>::Assoc: Read, (): Never
{
    let reader: &dyn Read = &wrap;
    let value = 7;
    let _ = reader.read(&value);
}
fn invoke<'a>(wrap: Wrap<'a>) -> isize
where Foo: Pick<'a>, <Foo as Pick<'a>>::Assoc: Read,
{
    let reader: &dyn Read = &wrap;
    let value = 7;
    reader.read(&value) as isize - 7
}
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let wrap = Wrap::< 'static> { pointer: identity, associated: identity };
    invoke::<'static>(wrap)
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
