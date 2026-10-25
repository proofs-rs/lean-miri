#![no_std]
#![no_main]

struct Wrapper<T: ?Sized> {
    tag: u32,
    callable: T,
}

// Separate positive fixture: built-in struct-tail unsizing, then virtual call.
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let bias = 1u32;
    let closure = |value: u32| value.wrapping_add(bias);
    let wrapper = Wrapper { tag: 7u32, callable: closure };
    let view: &Wrapper<dyn Fn(u32) -> u32> = &wrapper;
    ((view.callable)(8) as isize) - 9 + (view.tag as isize) - 7
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
