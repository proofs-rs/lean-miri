#![no_std]
#![feature(lang_items)]
// Repeated execution of the same caller_location site must keep runtime
// global identity behavior; immutable compiler evidence may be reused.
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
    let mut previous = 0;
    let mut round = 0;
    while round < 2 {
        let location = core::panic::Location::caller();
        let current = unsafe { miri_get_alloc_id((location as *const core::panic::Location).cast()) };
        if round == 1 && current == previous { return 1; }
        previous = current;
        round += 1;
    }
    42
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
