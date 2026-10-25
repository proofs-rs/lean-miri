use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

static DROPS: AtomicUsize = AtomicUsize::new(0);

struct DropCounter;

impl Drop for DropCounter {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

thread_local! {
    static TLS_COUNTER: DropCounter = const { DropCounter };
}

fn main() {
    let first = thread::spawn(|| TLS_COUNTER.with(|_| {}));
    first.join().expect("first thread panicked");
    assert_eq!(DROPS.load(Ordering::SeqCst), 1);

    let second = thread::spawn(|| TLS_COUNTER.with(|_| {}));
    second.join().expect("second thread panicked");
    assert_eq!(DROPS.load(Ordering::SeqCst), 2);
}
