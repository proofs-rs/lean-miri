#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
#![allow(dead_code)]
use std::{ops::Coroutine, pin::Pin};
pub fn source<T: Copy>(value: T) -> impl Coroutine<Yield=T, Return=T> {
    #[coroutine] move || { yield value; value }
}
pub fn root() {
    let mut a = source(7u8);
    let _ = unsafe { Pin::new_unchecked(&mut a) }.resume(());
    let mut b = source(11u64);
    let _ = unsafe { Pin::new_unchecked(&mut b) }.resume(());
}
