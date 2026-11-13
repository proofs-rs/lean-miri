#![no_std]
#![allow(dead_code)]
#[inline(never)] fn keep<T>(value:T) { core::hint::black_box(value); }
fn need_async<F:FnOnce(u16)->R,R>(value:F) { keep(value); }
pub fn query_async() { let bias=7u32; let callable=async move |value:u16| bias+value as u32;need_async(callable); }
pub fn async_root() {query_async();}
