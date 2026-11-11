#![feature(reborrow)]
use std::marker::{CoerceShared, Reborrow};
struct CustomMut<'a, T>(&'a mut T);
impl<'a, T> Reborrow for CustomMut<'a, T> {}
impl<'a, T> CoerceShared<CustomRef<'a, T>> for CustomMut<'a, T> {}
struct CustomRef<'a, T>(&'a T);
impl<'a, T> Clone for CustomRef<'a, T> { fn clone(&self) -> Self { Self(self.0) } }
impl<'a, T> Copy for CustomRef<'a, T> {}
fn read(value: CustomRef<'_, u32>) -> u32 { *value.0 }
pub fn identity() -> u32 {
    let mut value = 7;
    let source = CustomMut(&mut value);
    read(source)
}
