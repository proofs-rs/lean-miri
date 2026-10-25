use core::ffi::{c_char, c_void};

unsafe extern "C" {
    fn memcmp(left: *const c_void, right: *const c_void, len: usize) -> i32;
    fn memcpy(dest: *mut c_void, src: *const c_void, len: usize) -> *mut c_void;
    fn memset(dest: *mut c_void, byte: i32, len: usize) -> *mut c_void;
    fn memchr(ptr: *const c_void, byte: i32, len: usize) -> *mut c_void;
    fn strlen(ptr: *const c_char) -> usize;
    fn strnlen(ptr: *const c_char, limit: usize) -> usize;
}

// Reaching normal exit proves that every check succeeded. The failing branch
// deliberately loops, so the fixture does not import formatting/panic code.
fn main() {
    let source = [b'a', b'b', b'c', 0, b'x'];
    let mut copied = [0u8; 5];
    unsafe {
        if memcpy(copied.as_mut_ptr().cast(), source.as_ptr().cast(), 5)
            != copied.as_mut_ptr().cast() { loop {} }
        if memcmp(copied.as_ptr().cast(), source.as_ptr().cast(), 5) != 0 { loop {} }
        if memchr(copied.as_ptr().cast(), b'c' as i32, 5)
            != copied.as_mut_ptr().add(2).cast() { loop {} }
        if strlen(copied.as_ptr().cast()) != 3 { loop {} }
        if strnlen(copied.as_ptr().cast(), 2) != 2 { loop {} }
        if memset(copied.as_mut_ptr().add(4).cast(), b'Z' as i32, 1)
            != copied.as_mut_ptr().add(4).cast() { loop {} }
        if copied[0] != b'a' || copied[1] != b'b' || copied[2] != b'c'
            || copied[3] != 0 || copied[4] != b'Z' { loop {} }
    }
}
