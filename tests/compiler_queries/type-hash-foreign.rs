#![no_std]
#![feature(extern_types)]
unsafe extern "C" { pub type Foreign; }
pub fn nominal_hashes(pointer: *const Foreign, pair: (*const Foreign, *const Foreign)) {
    core::hint::black_box((pointer, pair));
}
