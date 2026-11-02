/// Duplicate the first `n` bytes into the following `n` bytes.
///
/// The bounds check ensures the source and destination ranges fit in `buf`.
/// For `n == 0`, the pointer operation is skipped.
pub fn duplicate_prefix(buf: &mut [u8], n: usize) -> bool {
    if n == 0 {
        return true;
    }
    if n > buf.len() / 2 {
        return false;
    }
    let p = buf.as_mut_ptr();
    unsafe {
        std::ptr::copy_nonoverlapping(p, p.add(n), n);
    }
    true
}
