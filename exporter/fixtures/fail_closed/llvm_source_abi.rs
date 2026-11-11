#![feature(link_llvm_intrinsics)]
#![no_std]
unsafe extern "llvm-intrinsic" {
    #[link_name = "llvm.x86.sse2.pause"] fn pause();
}
pub unsafe fn identity() { pause(); }
