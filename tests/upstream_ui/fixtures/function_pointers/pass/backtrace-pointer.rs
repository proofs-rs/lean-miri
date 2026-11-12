#[repr(C)]
struct MiriFrame {
    name_len: usize,
    filename_len: usize,
    lineno: u32,
    colno: u32,
    fn_ptr: *mut (),
}

extern "Rust" {
    fn miri_backtrace_size(flags: u64) -> usize;
    fn miri_get_backtrace(flags: u64, buf: *mut *mut ());
    fn miri_resolve_frame(ptr: *mut (), flags: u64) -> MiriFrame;
}

fn main() {
    unsafe {
        let count = miri_backtrace_size(0);
        assert!(count > 0);
        let mut frames = vec![std::ptr::null_mut(); count];
        miri_get_backtrace(1, frames.as_mut_ptr());
        let frame = miri_resolve_frame(frames[0], 1);
        assert!(!frame.fn_ptr.is_null());
    }
}
