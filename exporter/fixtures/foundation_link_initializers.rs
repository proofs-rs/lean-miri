extern "C" fn callback0() {}
extern "C" fn callback3(_: i32, _: *const *const u8, _: *const *const u8) {}
#[used]
#[unsafe(link_section = ".init_array")]
static INIT: extern "C" fn() = callback0;
#[used]
#[unsafe(link_section = ".init_array.00099")]
static PRIORITY: extern "C" fn(i32, *const *const u8, *const *const u8) = callback3;
fn main() {}
pub fn probe() -> extern "C" fn() { INIT }
pub fn probe3() -> extern "C" fn(i32, *const *const u8, *const *const u8) { PRIORITY }
