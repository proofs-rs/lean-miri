//! One finite QA construction corresponding to the closed Lean caller.
//! This is an unsafe diagnostic, not a proof of its Rust validity.
//! A/B are shared `UnsafeCell<()>` references; D/W come from their returned
//! pointer values. D's typed use ends before the first original write; V's
//! zero-length typed use ends before the second. Only the raw D is retained.
//! Miri assigns its own tags/addresses; no equality to Lean's tag literals is assumed.

use core::cell::UnsafeCell;

#[path = "../../examples/duplicate_prefix/duplicate_prefix.rs"]
mod target;

#[repr(C, align(2))]
struct Storage([u8; 2]);

fn main() {
    let mut storage = Storage([11, 22]);
    let original = (&raw mut storage.0) as *mut u8;

    // One expose/cast instance; A and B use copies of this same wildcard.
    let address = original as usize;
    let wildcard = address as *mut UnsafeCell<()>;
    let saved_raw_d = unsafe {
        let a: &UnsafeCell<()> = &*wildcard;
        let from_a = a as *const UnsafeCell<()> as *mut u8;
        let d: &mut [u8] = &mut *core::ptr::slice_from_raw_parts_mut(from_a, 2);
        d as *mut [u8] as *mut u8
    };

    unsafe {
        (original as *mut u16).write(0x160b);
    }
    let b: &UnsafeCell<()> = unsafe { &*wildcard };
    unsafe {
        let v: &mut [u8] = &mut *core::ptr::slice_from_raw_parts_mut(saved_raw_d, 0);
        // Keep this exposure in MIR without accessing any pointee bytes.
        core::hint::black_box(v as *mut [u8] as *mut u8 as usize);
    }
    unsafe {
        (original as *mut u16).write(0x160b);
    }
    let w: &mut [u8] = unsafe {
        let from_b = b as *const UnsafeCell<()> as *mut u8;
        &mut *core::ptr::slice_from_raw_parts_mut(from_b, 2)
    };
    assert!(target::duplicate_prefix(w, 1));
}
