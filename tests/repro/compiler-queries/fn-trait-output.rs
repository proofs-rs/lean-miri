#![no_std]
#![allow(dead_code)]
pub struct Token(pub u8);
#[inline(never)] pub fn keep<T>(value:T) { core::hint::black_box(value); }
pub fn plain(value:u16)->u32 { value as u32 }
pub unsafe fn unsafe_plain(value:u16)->u32 { value as u32 }
#[target_feature(enable="avx")] pub fn featured(value:u16)->u32 { value as u32 }
fn need_fn<F:Fn(u16)->u32>(value:F){keep(value)}
fn need_mut<F:FnMut(u16)->u32>(value:F){keep(value)}
fn need_once<F:FnOnce(u16)->u32>(value:F){keep(value)}
pub fn query_closures() {
 let shared=3u8; need_fn(move |value:u16| shared as u32+value as u32);
 let mut state=4u8; need_mut(move |value:u16| { state+=1;state as u32+value as u32 });
 let token=Token(9); need_once(move |value:u16| {let result=token.0 as u32+value as u32;core::mem::drop(token);result});
 let item=plain;keep(item);let item=unsafe_plain;keep(item);let item=featured;keep(item);
}
pub fn query_pointers(_safe:fn(u16)->u32,_unsafe:unsafe fn(u16)->u32,
 _c:extern "C" fn(u16)->u32,_variadic:unsafe extern "C" fn(u16,...)->u32) {}
pub fn query_unsized(_value:fn()->str) {}
pub fn fn_trait_root() { query_closures(); }
