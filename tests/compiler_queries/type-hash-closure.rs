#![no_std]
#![allow(dead_code, unused_must_use)]
pub struct Token(pub u16);
#[inline(never)]
pub fn generic_hashes<'a, T: Copy + 'a, const N: usize>(value: T, borrowed: &'a u16, array: [u8; N]) {
    let capture = move || (value, *borrowed, array);
    core::hint::black_box(capture);
}
pub fn closure_hashes(value: u32, borrowed: &'static u16, token: Token) {
    let empty = || 17u8;
    let scalar = move || value + 1;
    let reference = move || *borrowed;
    let pair = move || (value, borrowed);
    let higher_ranked = |value: &u8| *value;
    let once = move || token;
    let mut total = value;
    let mutate = || { total += 1; total };
    core::hint::black_box((empty, scalar, reference, pair, higher_ranked, once, mutate));
    generic_hashes(7u16, borrowed, [1u8, 2, 3]);
}
