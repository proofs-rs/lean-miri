#![allow(dead_code)]

pub trait Action<'a, T, const N: usize> {
    fn call(&self, input: &'a T) -> usize;
}
pub struct Concrete;
impl<'a> Action<'a, u32, 7> for Concrete {
    fn call(&self, input: &'a u32) -> usize { *input as usize + 7 }
}
#[inline(never)]
pub fn generic_rebase() -> usize {
    let concrete = Concrete;
    let object: &dyn Action<'_, u32, 7> = &concrete;
    object.call(&11)
}
