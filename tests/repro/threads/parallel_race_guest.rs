use std::cell::UnsafeCell;
use std::ptr;
use std::sync::{Arc, Barrier};
use std::thread;

struct Shared(UnsafeCell<u32>);
unsafe impl Sync for Shared {}
static SHARED: Shared = Shared(UnsafeCell::new(0));

// Both accesses occur after the same barrier but have no happens-before edge
// between them. Pinned Miri should report a data race, not normal exit.
fn main() {
    let barrier = Arc::new(Barrier::new(2));
    let child_barrier = Arc::clone(&barrier);
    let child = thread::spawn(move || {
        child_barrier.wait();
        unsafe { ptr::write_volatile(SHARED.0.get(), 1) }
    });
    barrier.wait();
    unsafe { let _ = ptr::read_volatile(SHARED.0.get()); }
    if child.join().is_err() {
        loop {}
    }
}
