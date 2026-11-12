#![no_std]
// The Rust scalar provider deliberately leaves foreign ABI classification residual.
pub fn residual(f:extern "C" fn(u8)->u8)->u8 {f(7)}
