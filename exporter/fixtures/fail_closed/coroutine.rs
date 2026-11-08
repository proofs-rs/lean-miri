#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use core::ops::Coroutine;
use core::pin::Pin;

pub fn root() {
    let mut coroutine = #[coroutine] || {
        yield 1_u32;
        2_u32
    };
    let _ = unsafe { Pin::new_unchecked(&mut coroutine) }.resume(());
}
