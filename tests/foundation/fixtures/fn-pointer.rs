pub fn identity(value: fn() -> ()) -> fn() -> () { value }
pub fn raw_identity(value: *const u8) -> *const u8 { value }
pub fn raw_mut_identity(value: *mut u8) -> *mut u8 { value }
pub fn higher(value: for<'a> fn(&'a u8) -> &'a u8) -> for<'a> fn(&'a u8) -> &'a u8 { value }
