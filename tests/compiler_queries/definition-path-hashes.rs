#![no_std]
pub struct Named { pub x: u8 }
pub struct Tuple(pub u8);
pub enum Choice { A, B(u8), C { x: u16 } }
pub struct Borrowed<'a, T = u8> { pub value: &'a T }
impl Named { pub fn value(&self) -> u8 { self.x } }
pub fn borrow<'a>(value: &'a u8) -> &'a u8 { value }
pub mod nested {
    #[inline(never)] pub fn one(value: u8) -> u8 { value }
    #[inline(never)] pub fn two(value: u8) -> u8 { value }
    #[inline(never)] pub fn three(value: u8) -> u8 { value }
    #[inline(never)] pub fn four(value: u8) -> u8 { value }
    #[inline(never)] pub fn five(value: u8) -> u8 { value }
}
pub fn definition_hash_root(
    values: *const (Named, Tuple, Choice, Borrowed<'static>, Option<u8>, core::marker::PhantomData<u8>),
    value: &'static u8,
) -> usize {
    let add = |x: usize| x + 1;
    let _ = borrow(value);
    let _ = Named { x: 3 }.value();
    let _ = nested::one(nested::two(nested::three(nested::four(nested::five(3)))));
    core::hint::black_box(values);
    add(3)
}
