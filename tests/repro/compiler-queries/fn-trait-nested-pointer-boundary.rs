#![no_std]
#![allow(dead_code)]
#[inline(never)] fn need<F:Fn(fn(u8)->u16)->u32>(value:F) {core::hint::black_box(value);}
pub fn query_nested(value:fn(fn(u8)->u16)->u32) {need(value);}
pub fn nested_root(value:fn(fn(u8)->u16)->u32) {query_nested(value);}
