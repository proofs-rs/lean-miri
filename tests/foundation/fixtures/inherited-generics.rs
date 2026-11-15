pub struct Carrier<T>(pub T);
impl<T> Carrier<T> {
    pub fn identity<U>(&self, value: U) -> U { value }
}
pub fn frame(value: u16) -> u16 { Carrier(0u8).identity(value) }
