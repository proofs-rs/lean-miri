// Linux mmap/mremap allocation ownership: copied bytes and zeroed growth.
// The pinned Miri implementation supports MREMAP_MAYMOVE without a fixed address.
use std::ffi::c_void;

unsafe extern "C" {
    fn malloc(size: usize) -> *mut c_void;
    fn realloc(address: *mut c_void, size: usize) -> *mut c_void;
    fn free(address: *mut c_void);
    fn mmap(address: *mut c_void, length: usize, protection: i32, flags: i32,
            fd: i32, offset: i64) -> *mut c_void;
    fn mremap(address: *mut c_void, old_size: usize, new_size: usize,
              flags: i32, ...) -> *mut c_void;
    fn munmap(address: *mut c_void, length: usize) -> i32;
}

fn main() {
    unsafe {
        let allocated = malloc(8).cast::<u8>();
        assert!(!allocated.is_null());
        *allocated = 0x3c;
        *allocated.add(7) = 0xc3;
        let reallocated = realloc(allocated.cast(), 16).cast::<u8>();
        assert!(!reallocated.is_null());
        assert_eq!(*reallocated, 0x3c);
        assert_eq!(*reallocated.add(7), 0xc3);
        free(reallocated.cast());

        let old = mmap(std::ptr::null_mut(), 4096, 3, 0x22, -1, 0);
        assert_ne!(old as usize, usize::MAX);
        assert_eq!((old as usize) % 4096, 0);
        let bytes = old.cast::<u8>();
        assert_eq!(*bytes, 0);
        *bytes = 0x5a;
        *bytes.add(4095) = 0xa5;
        let grown = mremap(old, 4096, 8192, 1);
        assert_ne!(grown as usize, usize::MAX);
        assert_eq!((grown as usize) % 4096, 0);
        let bytes = grown.cast::<u8>();
        assert_eq!(*bytes, 0x5a);
        assert_eq!(*bytes.add(4095), 0xa5);
        assert_eq!(*bytes.add(4096), 0);
        assert_eq!(*bytes.add(8191), 0);
        assert_eq!(munmap(grown, 8192), 0);
    }
}
