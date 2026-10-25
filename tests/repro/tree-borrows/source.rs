#![no_std]
#![no_main]

// Compact no_std miri_start adaptation of pinned Miri's
// fail/tree_borrows/parent_read_freezes_raw_mut.rs. The conditional consumes
// the parent read without pulling in assert_eq!'s formatting machinery.
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        let mut root = 6u8;
        let mref = &mut root;
        let ptr = mref as *mut u8;
        *ptr = 0;
        let parent_read = root;
        if parent_read != 0 {
            return 2;
        }
        *ptr = 0;
    }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
