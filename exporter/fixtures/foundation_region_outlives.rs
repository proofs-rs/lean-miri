pub fn reflexive<'a: 'a, T>() {}
pub fn use_reflexive<'a>() { reflexive::<'a, u8>(); }
pub fn type_outlives<'a, T: 'a>() {}
pub fn use_type_outlives<'a>() { type_outlives::<'a, u8>(); }
fn main() {}
