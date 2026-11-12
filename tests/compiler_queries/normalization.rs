#![allow(dead_code)]

// A fresh-export control for the alias-free identity normalization branch.
// Black boxes preserve reference, pointer, tuple and slice MIR operations.
pub fn constructors(value: &mut (u32, bool), bytes: &[u8]) -> usize {
    let pointer = std::hint::black_box(value as *mut (u32, bool));
    let reference = std::hint::black_box(value);
    let pair = std::hint::black_box((reference.0, reference.1));
    assert!(!pointer.is_null());
    assert_eq!(pair, (42, true));
    bytes.len()
}

fn main() {
    assert_eq!(constructors(&mut (42, true), &[1, 2, 3]), 3);
}
