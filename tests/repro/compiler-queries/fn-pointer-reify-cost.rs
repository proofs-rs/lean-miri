#![no_std]
#![feature(lang_items)]
// Small diagnostic control for repeated ReifyFnPointer casts, without std startup.
#[inline(never)]
fn target(value: i32) -> i32 { value + 1 }
#[lang = "termination"]
trait Termination { fn report(self) -> i32; }
impl Termination for i32 { fn report(self) -> i32 { self } }
#[lang = "start"]
fn source_start<T: Termination + 'static>(
    main: fn() -> T, _argc: isize, _argv: *const *const u8, _sigpipe: u8,
) -> isize { main().report() as isize }
#[unsafe(no_mangle)]
pub fn main() -> i32 {
    let first: fn(i32) -> i32 = target;
    let second: fn(i32) -> i32 = target;
    first(20) + second(20)
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
