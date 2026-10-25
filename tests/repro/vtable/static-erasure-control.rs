#![no_std]
#![no_main]
// Negative control for globals: the CTFE symbolic vtable for Borrowed<'static>
// also arrives with an already-canonical pair, despite the source lifetime.
trait Marker: Sync { fn value(&self) -> u8; }
struct Borrowed<'a>(&'a u8);
impl Marker for Borrowed<'_> { fn value(&self) -> u8 { *self.0 } }
static VALUE: u8 = 9;
static OBJECT: &dyn Marker = &Borrowed(&VALUE);
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize { OBJECT.value() as isize - 9 }
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
