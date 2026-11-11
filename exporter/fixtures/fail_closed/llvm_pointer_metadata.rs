#![feature(link_llvm_intrinsics)]
#![no_std]
// This pointer type is retained as metadata but never called.
pub fn identity(_function: unsafe extern "llvm-intrinsic" fn()) -> usize { core::mem::size_of::<unsafe extern "llvm-intrinsic" fn()>() }
