extern "Rust" {
    fn miri_resolve_frame(ptr: *mut (), flags: u64);
}

fn main() {
    unsafe {
        miri_resolve_frame(std::ptr::without_provenance_mut(1), 0); //~ ERROR: no provenance
    }
}
