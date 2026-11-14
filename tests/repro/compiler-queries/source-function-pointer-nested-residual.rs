#![no_std]
// Nested FnPtr children must be losslessly reified before source ABI admission.
pub fn nested(f:fn(fn(&dyn core::fmt::Debug)->u8)->u8,g:fn(&dyn core::fmt::Debug)->u8)->u8 {f(g)}
