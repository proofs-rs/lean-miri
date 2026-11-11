#![no_std]
use core::arch::x86_64::{__m128i, _mm_aesenc_si128};
#[target_feature(enable = "aes")]
pub unsafe fn identity(a: __m128i, b: __m128i) -> __m128i { _mm_aesenc_si128(a, b) }
