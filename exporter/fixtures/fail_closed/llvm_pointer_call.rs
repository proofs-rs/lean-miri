#![feature(link_llvm_intrinsics)]
#![no_std]
// A demanded normal ABI for this signature is undefined in the pinned compiler.
pub unsafe fn identity(function: unsafe extern "llvm-intrinsic" fn()) { function(); }
