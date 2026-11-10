#![no_std]

trait Concrete {
    type Item: ?Sized;
    const SIZE: usize;
}

struct Bytes;
impl Concrete for Bytes {
    type Item = [u8];
    const SIZE: usize = 7;
}

#[inline(never)]
fn resolved<T: Concrete>(value: *const T::Item) -> (*const T::Item, usize) {
    (value, T::SIZE)
}

pub fn root(value: *const [u8]) -> (*const [u8], usize) {
    resolved::<Bytes>(value)
}
