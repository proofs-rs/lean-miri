#![feature(link_llvm_intrinsics, simd_ffi)]
use std::arch::x86_64::__m128;
#[allow(improper_ctypes)]
unsafe extern "llvm-intrinsic" {
    #[link_name = "llvm.x86.sse2.pause"] fn pause();
    #[link_name = "llvm.x86.sse.min.ss"] fn minss(a: __m128, b: __m128) -> __m128;
}
fn main() {
    unsafe {
        pause();
        let a: __m128 = std::mem::transmute([1.0f32,8.0,9.0,10.0]);
        let b: __m128 = std::mem::transmute([2.0f32,3.0,4.0,5.0]);
        let result: [f32;4] = std::mem::transmute(minss(a,b));
        assert_eq!(result,[1.0,8.0,9.0,10.0]);
    }
}
