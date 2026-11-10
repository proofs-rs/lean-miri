#![no_std]

struct Checked<const N: usize>;
impl<const N: usize> Checked<N> {
    const VALID: () = assert!(N != 0);
}

#[inline(never)]
fn checked<const N: usize>() {
    let _ = Checked::<N>::VALID;
}

pub fn root() {
    checked::<0>();
}
