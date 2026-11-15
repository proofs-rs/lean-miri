// Finite local declaration and all its source impl headers; no query answers.
pub trait Marker {}
impl Marker for u8 {}
impl Marker for u32 {}
pub fn marked<T: Marker>(value: T) -> T { value }
