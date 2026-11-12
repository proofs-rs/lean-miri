#![allow(dead_code)]

pub struct Tail<T: ?Sized> { pub prefix: u32, pub tail: T }
pub enum Choice { A(u8), B(u64) }
pub union Either { pub byte: u8, pub word: u64 }
pub struct Empty;

// A fresh compiler export retains material for sized and unsized nested struct
// tails, empty/nonempty tuples, enum/union stop cases, Box and both pointer kinds.
#[inline(never)]
pub fn structural_types(
    boxed: Box<u32>,
    shared: &Tail<Tail<[u8]>>,
    mutable: &mut (u8, (u16, u32)),
    raw: *mut u64,
    empty: Empty,
    choice: Choice,
    union: Either,
) -> u32 {
    std::hint::black_box((shared, mutable, raw, empty, choice, union));
    *boxed
}
