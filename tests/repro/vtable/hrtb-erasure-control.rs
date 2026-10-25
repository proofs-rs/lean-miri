#![no_std]
#![no_main]
// Negative control: named source binders are already anonymous in the emitted
// vtable query. This does not cover a nonidentity erase/anonymize result.
trait Marker<'a> { fn value(&self, input: &'a u8) -> u8; }
struct Hrtb;
impl<'a> Marker<'a> for Hrtb { fn value(&self, input: &'a u8) -> u8 { *input } }
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let h = Hrtb;
    let object: &dyn for<'named> Marker<'named> = &h;
    // Same concrete type, distinct complete predicate arrays. Removing either
    // query must not let the consumer fall back to the other type-only match.
    let send: &(dyn for<'other> Marker<'other> + Send) = &h;
    object.value(&9) as isize + send.value(&9) as isize - 18
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
