#![allow(dead_code)]
pub type Replacement = for<'a> fn(&'a u32);
pub type TemplateFunction<T> = fn(T);
pub type TemplateTuple<T> = (T, fn(T));
pub type TemplateNested<T> = fn(fn(T));
pub type TemplateRegion<'a, T> = (&'a T, fn(&'a T));
pub type TemplateArray<const N: usize> = fn([u8; N]);
pub type TemplateMixed<'a, T, const N: usize> = (&'a [T; N], fn([T; N]));
pub type TemplateDynamic<'a, T> = &'a dyn Iterator<Item = T>;
pub struct TemplateWrapper<T>(pub T, pub fn(T));
pub type TemplateAdt<T> = TemplateWrapper<T>;
pub enum TemplateEnum<T> { Empty, Value(T) }
#[allow(non_snake_case)]
pub fn TemplateFn<T>(value: T) -> T { value }
