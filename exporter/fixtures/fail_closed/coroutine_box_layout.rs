#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::Coroutine;

pub fn root() {
    let mut state = Box::pin(#[coroutine] || {
        yield 7_u32;
        11_u32
    });
    let _ = state.as_mut().resume(());
    let closure: fn(u32) -> u32 = |value| value + 1;
    assert_eq!(std::hint::black_box(closure)(1), 2);
}
