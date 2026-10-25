use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

// Reaching normal exit proves thread completion, release/acquire visibility,
// and mutex-protected state. Failure deliberately loops without panic
// formatting dependencies.
fn main() {
    let shared = Arc::new((AtomicUsize::new(0), Mutex::new(0usize)));
    let child_shared = Arc::clone(&shared);
    let child = thread::spawn(move || {
        child_shared.0.store(1, Ordering::Release);
        match child_shared.1.lock() {
            Ok(mut guard) => *guard = 7,
            Err(_) => loop {},
        }
    });
    if child.join().is_err() {
        loop {}
    }
    if shared.0.load(Ordering::Acquire) != 1 {
        loop {}
    }
    match shared.1.lock() {
        Ok(guard) if *guard == 7 => (),
        _ => loop {},
    }
}
