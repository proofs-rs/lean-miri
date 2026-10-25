//! Manually transcribed source-side integer/bool/char branches from pinned operator.rs.
//! These finite comparisons do not establish full interpreter equivalence.
fn main() {
    // ScalarInt truncate_from_uint to a one-byte unsigned result.
    let add = (255u128).overflowing_add(2);
    let wrapped = add.0 as u8;
    let overflow = add.1 || add.0 != wrapped as u128;
    assert_eq!((wrapped, overflow), (1, true));
    assert_eq!(true ^ true, false);
    assert_eq!('a' < 'z', true);
    assert_eq!('z'.cmp(&'a') as i8, 1);
    assert_eq!(!15u8, 240);
    // Signed RHS Euclidean modulo and LHS width govern shifts.
    let amount = (-1i128).rem_euclid(8) as u32;
    assert_eq!((1u128 << amount) as u8, 128);
    assert_eq!((i8::MIN as i128).wrapping_neg() as i8, i8::MIN);
    println!("scalar source helper checks passed (7)");
}
