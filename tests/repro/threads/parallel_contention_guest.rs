use std::cell::Cell;
use std::process;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Condvar, Mutex, RwLock};
use std::thread;

static TLS_DROPS: AtomicUsize = AtomicUsize::new(0);

struct TlsDrop;
impl Drop for TlsDrop {
    fn drop(&mut self) {
        TLS_DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

thread_local! {
    static WORKER_TLS: Cell<Option<TlsDrop>> = const { Cell::new(None) };
}

fn fail() -> ! {
    process::exit(1)
}

enum TryLockStatus { Blocked, Acquired }

fn lock_and_check(pair: &Arc<(Mutex<bool>, Condvar)>) -> TryLockStatus {
    match pair.0.try_lock() {
        Err(std::sync::TryLockError::WouldBlock) => TryLockStatus::Blocked,
        Ok(guard) => {
            drop(guard);
            TryLockStatus::Acquired
        }
        Err(std::sync::TryLockError::Poisoned(_)) => fail(),
    }
}

fn main() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let (ready_tx, ready_rx) = mpsc::sync_channel::<()>(0);
    let (ack_tx, ack_rx) = mpsc::sync_channel::<()>(0);

    let worker_pair = Arc::clone(&pair);
    let worker = thread::spawn(move || {
        WORKER_TLS.with(|slot| slot.set(Some(TlsDrop)));

        // Notify while holding the predicate mutex, then wait for main's
        // acknowledgement so the lock remains held during its try_lock check.
        let (lock, cv) = &*worker_pair;
        let mut proceed = match lock.lock() {
            Ok(guard) => guard,
            Err(_) => fail(),
        };
        if ready_tx.send(()).is_err() {
            fail();
        }
        if ack_rx.recv().is_err() {
            fail();
        }
        while !*proceed {
            proceed = match cv.wait(proceed) {
                Ok(guard) => guard,
                Err(_) => fail(),
            };
        }
    });

    if ready_rx.recv().is_err() {
        fail();
    }
    if !matches!(lock_and_check(&pair), TryLockStatus::Blocked) {
        fail();
    }
    if ack_tx.send(()).is_err() {
        fail();
    }
    // The worker still owns the mutex until it enters cv.wait, so this lock
    // blocks until wait atomically releases the mutex.
    let (lock, cv) = &*pair;
    let mut proceed = match lock.lock() {
        Ok(guard) => guard,
        Err(_) => fail(),
    };
    *proceed = true;
    cv.notify_one();
    drop(proceed);

    // A live read guard makes try_write fail deterministically. After it is
    // dropped, the worker's write lock succeeds and is observed after join.
    let value = Arc::new(RwLock::new(0usize));
    let read_guard = match value.read() {
        Ok(guard) => guard,
        Err(_) => fail(),
    };
    if value.try_write().is_ok() {
        fail();
    }
    drop(read_guard);
    let writer_value = Arc::clone(&value);
    let writer = thread::spawn(move || {
        let mut guard = match writer_value.write() {
            Ok(guard) => guard,
            Err(_) => fail(),
        };
        *guard = 1;
    });

    if worker.join().is_err() {
        fail();
    }
    match writer.join() {
        Ok(()) => (),
        Err(_) => fail(),
    }
    let observed = match value.read() {
        Ok(guard) => *guard,
        Err(_) => fail(),
    };
    if observed != 1 || TLS_DROPS.load(Ordering::SeqCst) != 1 {
        fail();
    }
}
