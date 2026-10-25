#![no_std]
#![no_main]

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
    fn miri_resolve_frame(frame: *mut (), flags: u64) -> MiriFrame;
    fn miri_resolve_frame_names(
        frame: *mut (),
        flags: u64,
        name_buf: *mut (),
        filename_buf: *mut (),
    );
}

const FRAME_LIMIT: usize = 32;
const NAME_LIMIT: usize = 256;
const FILE_LIMIT: usize = 256;

fn equal(bytes: &[u8], expected: &[u8]) -> bool {
    if bytes.len() != expected.len() {
        return false;
    }
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != expected[index] {
            return false;
        }
        index += 1;
    }
    true
}

#[inline(never)]
fn trace_outer() -> i32 {
    trace_middle()
}

#[inline(never)]
fn trace_middle() -> i32 {
    trace_leaf()
}

#[inline(never)]
fn trace_leaf() -> i32 {
    unsafe {
        let count = miri_backtrace_size(0);
        if count < 3 || count > FRAME_LIMIT {
            return 20;
        }

        let mut frames = [core::ptr::null_mut::<()>(); FRAME_LIMIT];
        miri_get_backtrace(1, frames.as_mut_ptr());

        let mut saw_leaf = false;
        let mut saw_outer = false;
        let mut index = 0;
        while index < count {
            let frame = miri_resolve_frame(frames[index], 1);
            if frame.name_len == 0 || frame.name_len > NAME_LIMIT ||
                frame.filename_len == 0 || frame.filename_len > FILE_LIMIT ||
                frame.lineno == 0 || frame.colno == 0 {
                return 21;
            }

            let mut name = [0u8; NAME_LIMIT];
            let mut filename = [0u8; FILE_LIMIT];
            miri_resolve_frame_names(
                frames[index],
                0,
                name.as_mut_ptr().cast(),
                filename.as_mut_ptr().cast(),
            );

            if equal(&name[..frame.name_len], b"trace_leaf") {
                if frame.fn_ptr != trace_leaf as *mut () {
                    return 22;
                }
                saw_leaf = true;
            }
            if equal(&name[..frame.name_len], b"trace_outer") {
                saw_outer = true;
            }
            index += 1;
        }

        if saw_leaf && saw_outer { 0 } else { 23 }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    trace_outer() as isize
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
