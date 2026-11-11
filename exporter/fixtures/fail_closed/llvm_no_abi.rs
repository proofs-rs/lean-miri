#![feature(link_llvm_intrinsics, simd_ffi)]
#![no_std]
use core::arch::x86_64::__m128;
#[allow(improper_ctypes)]
unsafe extern "C" {
    #[link_name = "llvm.x86.sse2.pause"] fn pause();
    #[link_name = "llvm.x86.sse.min.ss"] fn minss(a: __m128, b: __m128) -> __m128;
}
pub unsafe fn identity(a: __m128, b: __m128) -> __m128 {
    pause();
    minss(a, b)
}
