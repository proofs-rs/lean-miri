#![no_std]
#![feature(lang_items)]

use core::panic::PanicInfo;

static mut TRACE: u32 = 0;

fn append(digit: u32) {
    let trace = core::ptr::addr_of_mut!(TRACE);
    unsafe {
        let current = trace.read();
        trace.write(current * 10 + digit);
    }
}

unsafe extern "C" fn ctor_first() {
    append(1);
}

unsafe extern "C" fn ctor_second() {
    append(2);
}

// The pinned query returns [second, first], and pinned Miri's constructor
// stack pops that order in reverse. The ordinary `main` below succeeds only
// if startup ran first then second before entering it.
#[used]
#[unsafe(link_section = ".init_array")]
static INIT: [unsafe extern "C" fn(); 2] = [ctor_second, ctor_first];

#[lang = "termination"]
trait Termination {
    fn report(self) -> i32;
}
impl Termination for i32 {
    fn report(self) -> i32 { self }
}

#[lang = "start"]
fn source_start<T: Termination + 'static>(
    main: fn() -> T,
    _argc: isize,
    _argv: *const *const u8,
    _sigpipe: u8,
) -> isize {
    main().report() as isize
}

#[unsafe(no_mangle)]
pub fn main() -> i32 {
    let trace = unsafe { core::ptr::addr_of!(TRACE).read() };
    if trace == 12 { 0 } else { 1 }
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop { core::hint::spin_loop(); }
}
