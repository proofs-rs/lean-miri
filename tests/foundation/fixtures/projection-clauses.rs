pub fn identity<F: FnOnce() -> u8>(value: F) -> F { value }
pub fn pointer(value: fn() -> u8) -> fn() -> u8 { identity(value) }
