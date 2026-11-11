#![feature(link_llvm_intrinsics)]
unsafe extern "C" {
    #[link_name = "llvm.ctpop.v4i32"] fn vector_count(scalar: u32) -> u32;
}
fn main() { unsafe { let _ = vector_count(1); } }
