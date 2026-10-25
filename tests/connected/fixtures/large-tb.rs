#![no_std]
#![no_main]

// Adapted from pinned Miri's fail/tree_borrows/parent_read_freezes_raw_mut.rs
// by replacing only the ordinary `main` entry with the no_std MiriStart ABI.
#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        let mut root = 6u8;
        let mref = &mut root;
        let ptr = mref as *mut u8;
        *ptr = 0; // Write through the derived raw pointer.
        assert_eq!(root, 0); // Parent read freezes the raw-mut child under TB.
        *ptr = 0; // Expected Tree Borrows UB.
    }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
