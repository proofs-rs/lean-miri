#![allow(dead_code)]

use std::mem::{ManuallyDrop, MaybeUninit};

pub struct Droppy(pub u32);
impl Drop for Droppy {
    fn drop(&mut self) { std::hint::black_box(self.0); }
}
pub struct Plain<T>(pub T);
pub enum Nested {
    Empty,
    Suppressed(ManuallyDrop<Droppy>),
    Zero([Droppy; 0]),
    Active(Plain<(u32, Droppy)>),
}
pub union Union {
    pub empty: (),
    pub value: ManuallyDrop<Droppy>,
}

// Explicit source-demanded material covers destructor/field recursion,
// ManuallyDrop and MaybeUninit (union), empty/nonempty arrays and closures.
#[inline(never)]
pub fn needs_drop_types(
    active: Nested,
    suppressed: ManuallyDrop<Droppy>,
    uninitialized: MaybeUninit<Droppy>,
    union: Union,
    zero: [Droppy; 0],
    nonzero: [Droppy; 2],
    plain: Plain<u32>,
    captured: Droppy,
) {
    std::hint::black_box((active, suppressed, uninitialized, union, zero, nonzero, plain));
    let closure = move || std::hint::black_box(captured);
    std::hint::black_box(closure)();
}
