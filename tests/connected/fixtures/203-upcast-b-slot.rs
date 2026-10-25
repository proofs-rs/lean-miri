#![no_std]
#![no_main]
trait A { fn a(&self) -> u32; }
trait B { fn b(&self) -> u32; }
trait Derived: A + B {}
struct Value { a: u32, b: u32 }
impl A for Value { fn a(&self) -> u32 { self.a } }
impl B for Value { fn b(&self) -> u32 { self.b } }
impl Derived for Value {}

// New fixture: second-supertrait upcast. Exact slot evidence is checked later.
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let value = Value { a: 9, b: 11 };
    let derived: &dyn Derived = &value;
    let base: &dyn B = derived;
    (base.b() as isize) - 11
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
