// A finite generic source impl, not enumerated monomorphic trait answers.
pub trait Marker {}
impl<T: Copy> Marker for [T; 3] {}
pub fn marked<T: Marker>(value: T) -> T { value }
