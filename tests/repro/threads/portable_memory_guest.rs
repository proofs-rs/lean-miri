use core::ffi::{c_char, c_void};

unsafe extern "C" {
    fn memcmp(left: *const c_void, right: *const c_void, len: usize) -> i32;
    fn memcpy(dest: *mut c_void, src: *const c_void, len: usize) -> *mut c_void;
    fn memset(dest: *mut c_void, byte: i32, len: usize) -> *mut c_void;
    fn memchr(ptr: *const c_void, byte: i32, len: usize) -> *mut c_void;
    fn strlen(ptr: *const c_char) -> usize;
    fn strnlen(ptr: *const c_char, limit: usize) -> usize;
}

fn main() {
    let source = [b'a', b'b', b'c', 0, b'x'];
    let mut copied = [0u8; 5];
    unsafe {
        assert_eq!(memcpy(copied.as_mut_ptr().cast(), source.as_ptr().cast(), 5), copied.as_mut_ptr().cast());
        assert_eq!(memcmp(copied.as_ptr().cast(), source.as_ptr().cast(), 5), 0);
        assert_eq!(memchr(copied.as_ptr().cast(), b'c' as i32, 5), copied.as_mut_ptr().add(2).cast());
        assert_eq!(strlen(copied.as_ptr().cast()), 3);
        assert_eq!(strnlen(copied.as_ptr().cast(), 2), 2);
        assert_eq!(memset(copied.as_mut_ptr().add(4).cast(), b'Z' as i32, 1), copied.as_mut_ptr().add(4).cast());
        assert_eq!(copied, [b'a', b'b', b'c', 0, b'Z']);
    }
}
