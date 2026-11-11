#![feature(link_llvm_intrinsics)]
unsafe extern "C" {
    #[link_name = "llvm.x86.lean_miri_unknown"] fn unknown();
}
fn main() { unsafe { unknown(); } }
