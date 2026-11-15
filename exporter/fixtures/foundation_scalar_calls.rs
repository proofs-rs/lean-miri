// Separate widths exercise scalar transport through real direct-call frames.
pub fn identity<T: Copy>(value: T) -> T { value }
pub fn call_u16(value: u16) -> u16 { identity(value) }
pub fn call_usize(value: usize) -> usize { identity(value) }
