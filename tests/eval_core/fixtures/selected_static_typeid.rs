#![allow(dead_code)]

use core::any::TypeId;

#[no_mangle]
pub static SELECTED_STATIC: u32 = 0x5a17_0162;

/// This direct monomorphic call makes the source `type_id` intrinsic demand
/// observable to the opt-in allocator-world producer.
#[inline(never)]
pub fn root() -> u32 {
    let id = TypeId::of::<u32>();
    core::hint::black_box(id);
    // SAFETY: the exported static is immutable and has a valid u32 initializer.
    unsafe { core::ptr::read_volatile(&SELECTED_STATIC) }
}
