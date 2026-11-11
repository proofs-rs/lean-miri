#![feature(link_llvm_intrinsics)]
#[unsafe(export_name = "llvm.x86.sse2.pause")]
pub unsafe extern "C" fn conflicting_export() {}
unsafe extern "C" {
    #[link_name = "llvm.x86.sse2.pause"] fn pause();
}
fn main() { unsafe { pause(); } }
