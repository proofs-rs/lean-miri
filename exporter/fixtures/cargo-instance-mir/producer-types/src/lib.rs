#![no_std]
#![feature(rustc_attrs)]
#![allow(internal_features)]

pub struct Pair(pub u16, pub u32);

pub enum Token {
    Empty,
    Number(u32),
    Pair(u16, u32),
}

/// This function's MIR is retained for CTFE and has no optimized-MIR body.
#[rustc_comptime]
pub fn compile_time_add(left: u32, right: u32) -> u32 {
    left + right
}

pub struct Opcode;

impl Opcode {
    /// Associated-function variant of the CTFE-only MIR case.
    #[rustc_comptime]
    pub fn compile_time_xor(value: u32, mask: u32) -> u32 {
        value ^ mask
    }
}
