#![feature(coroutines,coroutine_trait,stmt_expr_attributes)]
#![allow(dead_code)]
use std::ops::Coroutine;
pub fn make<T:Copy>(value:T)->impl Coroutine<Yield=T,Return=T> {
    #[coroutine] move || {yield value;value}
}
pub fn root() {
    let first=make(7u8);drop(first);
    let repeated=make(11u8);drop(repeated);
    let distinct=make(13u64);drop(distinct);
}
