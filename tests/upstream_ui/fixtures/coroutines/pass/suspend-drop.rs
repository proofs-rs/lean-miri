//@revisions: tree tree_implicit_writes
//@[tree]compile-flags: -Zmiri-tree-borrows
//@[tree_implicit_writes]compile-flags: -Zmiri-tree-borrows -Zmiri-tree-borrows-implicit-writes
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::cell::Cell;
use std::ops::{Coroutine, CoroutineState};
use std::pin::pin;

struct CountDrop<'a>(&'a Cell<u32>);
impl Drop for CountDrop<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

fn main() {
    let drops = Cell::new(0);
    {
        let mut suspended = pin!(#[coroutine] || {
            let _guard = CountDrop(&drops);
            let bytes = [7_u8, 11, 13];
            yield bytes[0];
            bytes[1]
        });
        assert_eq!(suspended.as_mut().resume(()), CoroutineState::Yielded(7));
        assert_eq!(drops.get(), 0);
    }
    assert_eq!(drops.get(), 1);
    {
        let mut completed = pin!(#[coroutine] || {
            let _guard = CountDrop(&drops);
            yield 17_u8;
            19_u8
        });
        assert_eq!(completed.as_mut().resume(()), CoroutineState::Yielded(17));
        assert_eq!(completed.as_mut().resume(()), CoroutineState::Complete(19));
        assert_eq!(drops.get(), 2);
    }
    assert_eq!(drops.get(), 2);
}
