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

fn main() {
    let bytes = [3_u8, 5, 7];
    let slice: &[u8] = &bytes;
    let (pointer, size) = resolved::<Bytes>(slice as *const [u8]);
    assert_eq!(size, 7);
    let roundtrip = unsafe { &*pointer };
    assert_eq!(roundtrip.len(), 3);
    assert_eq!(roundtrip[1], 5);
}
