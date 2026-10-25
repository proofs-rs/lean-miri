pub static DATA: u32 = 41;
#[inline(never)]
pub fn leaf(value: u32) -> u32 { value + 1 }
#[inline(never)]
pub fn nested(value: u32) -> u32 { leaf(DATA + value) }
pub fn root(value: u32) -> u32 { nested(value) }
