#![no_std]
#![no_main]

struct Wrapper<T>(T);

#[inline(never)]
fn name<T>() -> &'static str {
    core::any::type_name::<T>()
}

#[unsafe(no_mangle)]
fn miri_start(_: isize, _: *const *const u8) -> isize {
    let wrapped = name::<Wrapper<u16>>();
    assert_eq!(wrapped.len(), 31);
    assert_eq!(wrapped.as_bytes()[0], b't');
    assert_eq!(name::<(u8, u64)>(), "(u8, u64)");
    assert_eq!(name::<[u32; 3]>(), "[u32; 3]");
    0
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
