#![no_std]
#![feature(lang_items)]
static STATIC_VALUE: u32 = 41;
#[inline(never)]
fn target_function() {}
unsafe extern "Rust" {
    fn miri_get_alloc_id(ptr: *const ()) -> u64;
}
#[lang = "termination"]
trait Termination { fn report(self) -> i32; }
impl Termination for i32 { fn report(self) -> i32 { self } }
#[lang = "start"]
fn source_start<T: Termination + 'static>(
    main: fn() -> T, _argc: isize, _argv: *const *const u8, _sigpipe: u8,
) -> isize { main().report() as isize }
#[unsafe(no_mangle)]
pub fn main() -> i32 {
    let local_value = 17u32;
    let local = unsafe { miri_get_alloc_id((&local_value as *const u32).cast::<()>()) };
    let global = unsafe { miri_get_alloc_id((&STATIC_VALUE as *const u32).cast::<()>()) };
    let function = unsafe { miri_get_alloc_id(target_function as *const ()) };
    if local >= 1024 || global >= 1024 || function >= 1024 { return i32::MAX; }
    (local | (global << 10) | (function << 20)) as i32
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
