pub fn two(_: for<'a, 'b> unsafe fn(&'a u8, &'b mut u16) -> u32) {}
pub fn nested(_: for<'a> fn(for<'b> fn(&'a u8, &'b u8))) {}
fn main() {}
