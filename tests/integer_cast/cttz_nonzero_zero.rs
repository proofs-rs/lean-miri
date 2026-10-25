#![feature(core_intrinsics)]
#![allow(internal_features)]

fn main() {
    let input = std::hint::black_box(0u8);
    let _ = unsafe { core::intrinsics::cttz_nonzero(input) };
}
