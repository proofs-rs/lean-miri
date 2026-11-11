#![feature(link_llvm_intrinsics)]
unsafe extern "C" {
    #[link_name = "llvm.x86.sse2.pause"] fn pause(extra: u32);
}
fn main() {
    unsafe { pause(1); }
}
