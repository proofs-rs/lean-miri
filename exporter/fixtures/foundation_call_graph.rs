#[inline(never)]
pub fn identity<T: Copy>(value: T) -> T { value }
#[inline(never)]
pub fn middle<T: Copy>(value: T) -> T { identity(value) }
pub fn chain(value: u16) -> u16 { middle(value) }
pub fn twice(value: u16) -> u16 {
    let value = identity(value);
    identity(value)
}
#[allow(unconditional_recursion)]
pub fn recursive(value: u16) -> u16 { recursive(value) }
pub fn mutual_a(value: u16) -> u16 { mutual_b(value) }
pub fn mutual_b(value: u16) -> u16 { mutual_a(value) }
