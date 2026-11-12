#![allow(dead_code)]
pub type Replacement = for<'a> fn(&'a u32);
pub type TemplateFunction<T> = fn(T);
pub type TemplateTuple<T> = (T, fn(T));
pub type TemplateNested<T> = fn(fn(T));
pub type TemplateRegion<'a, T> = (&'a T, fn(&'a T));
pub type TemplateArray<const N: usize> = fn([u8; N]);
pub type TemplateMixed<'a, T, const N: usize> = (&'a [T; N], fn([T; N]));
pub type TemplateDynamic<'a, T> = &'a dyn Iterator<Item = T>;
pub struct Wrapper<T>(pub T);
pub type TemplateAdt<T> = Wrapper<T>;
