//@compile-flags: -C target-feature=+aes
use std::arch::x86_64::{__m128i, _mm_aesenc_si128};
fn main() {
    unsafe {
        let zero: __m128i = std::mem::transmute([0u8; 16]);
        let result: [u8;16] = std::mem::transmute(_mm_aesenc_si128(zero, zero));
        assert_eq!(result, [0x63;16]);
    }
}
