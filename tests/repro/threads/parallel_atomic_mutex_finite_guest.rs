use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

// A finite outcome distinguishes a failed check from an interpreter timeout.
// Normal exit still requires the child, atomic, and mutex observations.
fn main() {
    let shared = Arc::new((AtomicUsize::new(0), Mutex::new(0usize)));
    let child_shared = Arc::clone(&shared);
    let child = thread::spawn(move || {
        child_shared.0.store(1, Ordering::Release);
        match child_shared.1.lock() {
            Ok(mut guard) => *guard = 7,
            Err(_) => process::exit(1),
        }
    });
    if child.join().is_err() {
        process::exit(1);
    }
    if shared.0.load(Ordering::Acquire) != 1 {
        process::exit(1);
    }
    match shared.1.lock() {
        Ok(guard) if *guard == 7 => (),
        _ => process::exit(1),
    }
}
