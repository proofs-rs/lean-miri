#![no_std]
#![feature(lang_items)]

#[lang = "start"]
fn start<T>(main: fn() -> T, _argc: isize, _argv: *const *const u8, _sigpipe: u8) -> isize {
    main();
    0
}

// The template MIR contains an incomplete symbolic ConstKind::Param N.
// The executable instance uses N=3 and must initialize the last array element.
fn repeat<const N: usize>() -> usize {
    let data = [7_u8; N];
    data[2] as usize + data.len()
}

fn main() {
    assert!(repeat::<3>() == 10);
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
