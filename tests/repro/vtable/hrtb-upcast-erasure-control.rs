#![no_std]
#![no_main]
// Second-supertrait upcast: the parent table has a real TraitVPtr to B.
// Its HRTB destination and the erased child query stay distinct complete pairs.
trait A<'a> { fn a(&self, value: &'a u8) -> u8; }
trait B<'a> { fn b(&self, value: &'a u8) -> u8; }
trait Derived: for<'a> A<'a> + for<'b> B<'b> {}
struct Value;
impl<'a> A<'a> for Value { fn a(&self, value: &'a u8) -> u8 { *value } }
impl<'a> B<'a> for Value { fn b(&self, value: &'a u8) -> u8 { *value } }
impl Derived for Value {}
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let value = Value;
    let derived: &dyn Derived = &value;
    let base: &dyn for<'named> B<'named> = derived;
    base.b(&9) as isize - 9
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
