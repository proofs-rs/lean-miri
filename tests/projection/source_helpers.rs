//! Manually transcribed arithmetic control flow from pinned interpret/projection.rs.
//! Independent source-side checks; this is not an interpreter equivalence proof.
fn constant_index(n: u64, offset: u64, min_length: u64, from_end: bool) -> Result<u64, (u64, u64)> {
    if n < min_length { return Err((min_length, n)); }
    let index = if from_end {
        assert!(0 < offset && offset <= min_length);
        n.checked_sub(offset).unwrap()
    } else {
        assert!(offset < min_length);
        offset
    };
    Ok(index)
}
fn subslice_to(len: u64, from: u64, to: u64) -> Result<u64, (u64, u64)> {
    if from.checked_add(to).is_none_or(|to| to > len) {
        return Err((len, from.saturating_add(to)));
    }
    Ok(len.checked_sub(to).unwrap())
}
fn compute_size_in_bytes(stride: u64, count: u64, max_size_of_val: u64) -> Option<u64> {
    stride.checked_mul(count).filter(|&total| total <= max_size_of_val)
}
fn main() {
    assert_eq!(compute_size_in_bytes(4, 2, 8), Some(8));
    assert_eq!(compute_size_in_bytes(4, 2, 7), None);
    assert_eq!(compute_size_in_bytes(16384, 2, 32768), Some(32768));
    assert_eq!(compute_size_in_bytes(16384, 2, 32767), None);
    assert_eq!(compute_size_in_bytes(u64::MAX, 2, u64::MAX), None);
    assert_eq!(constant_index(2, 0, 3, true), Err((3, 2)));
    assert_eq!(constant_index(8, 2, 3, true), Ok(6));
    assert_eq!(constant_index(8, 2, 3, false), Ok(2));
    assert_eq!(subslice_to(3, 2, 2), Err((3, 4)));
    assert_eq!(subslice_to(u64::MAX, u64::MAX, 1), Err((u64::MAX, u64::MAX)));
    assert_eq!(subslice_to(8, 2, 3), Ok(5));
    println!("projection source helper checks passed");
}
