#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
#![allow(dead_code)]
use std::ops::Coroutine;
#[inline(never)] pub fn helper<T: Copy>(value:T)->T { value }
pub fn field<T: Copy>(value:(T,T))->impl Coroutine<Yield=T,Return=T> {
 #[coroutine] move || { yield value.0; value.1 }
}
pub fn index<T: Copy>(value:[T;3],index:usize)->impl Coroutine<Yield=T,Return=T> {
 #[coroutine] move || { yield value[index]; value[1] }
}
pub fn subslice<'a>(value:&'a [u8])->impl Coroutine<Yield=&'a [u8],Return=()>+'a {
 #[coroutine] move || { yield &value[1..]; }
}
pub fn cast(value:u16)->impl Coroutine<Yield=u8,Return=()> {
 #[coroutine] move || { yield value as u8; }
}
pub fn reference(mut value:u8)->impl Coroutine<Yield=u8,Return=()> {
 #[coroutine] move || { let reference=&mut value; *reference=3; yield *reference; }
}
pub fn direct_call<T: Copy>(value:T)->impl Coroutine<Yield=T,Return=T> {
 #[coroutine] move || { yield helper(value); helper(value) }
}
pub fn raw_pointer(value:u8)->impl Coroutine<Yield=u8,Return=()> {
 #[coroutine] move || { let address=&raw const value; yield unsafe {*address}; }
}
pub fn binary(value:u8)->impl Coroutine<Yield=u8,Return=()> {
 #[coroutine] move || { yield value+1; }
}
pub fn repeat(value:u8)->impl Coroutine<Yield=[u8;3],Return=()> {
 #[coroutine] move || { yield [value;3]; }
}
pub fn ordinary_field<T:Copy>(value:(T,T))->T {value.0}
pub fn ordinary_index<T:Copy>(value:[T;3],index:usize)->T {value[index]}
pub fn ordinary_subslice(value:&[u8])->&[u8] {&value[1..]}
pub fn ordinary_cast(value:u16)->u8 {value as u8}
pub fn ordinary_reference(value:&mut u8)->u8 {*value=3; *value}
pub fn ordinary_direct_call<T:Copy>(value:T)->T {helper(value)}
pub fn ordinary_raw_pointer(value:&u8)->*const u8 {&raw const *value}
pub fn ordinary_binary(value:u8)->u8 {value+1}
pub fn ordinary_repeat(value:u8)->[u8;3] {[value;3]}
pub fn constant_index<T:Copy>(value:[T;3])->impl Coroutine<Yield=T,Return=T> {
 #[coroutine] move || { let [head,_,_]=value; yield head; head }
}
pub fn subslice_pattern<T:Copy>(value:[T;3])->impl Coroutine<Yield=[T;2],Return=()> {
 #[coroutine] move || { let [_,tail @ ..]=value; yield tail; }
}
pub fn ordinary_constant_index<T:Copy>(value:[T;3])->T {let [head,_,_]=value;head}
pub fn ordinary_subslice_pattern<T:Copy>(value:[T;3])->[T;2] {let [_,tail @ ..]=value;tail}

pub fn root() {
    use std::pin::Pin;
    let _ = ordinary_field((7u8,9u8));
    let _ = ordinary_constant_index([1u8,2,3]);
    let _ = ordinary_subslice_pattern([1u8,2,3]);
    let _ = ordinary_cast(257u16);
    let mut value=7u8;
    let _ = ordinary_reference(&mut value);
    let _ = ordinary_direct_call(11u64);
    let _ = ordinary_fn_item_local(17u64);
    let _ = ordinary_raw_pointer(&value);
    let mut a=field((3u8,5u8));let _=unsafe{Pin::new_unchecked(&mut a)}.resume(());
    let mut b=cast(259u16);let _=unsafe{Pin::new_unchecked(&mut b)}.resume(());
    let mut c=reference(7u8);let _=unsafe{Pin::new_unchecked(&mut c)}.resume(());
    let mut d=direct_call(13u64);let _=unsafe{Pin::new_unchecked(&mut d)}.resume(());
    let mut e=constant_index([17u8,19,23]);let _=unsafe{Pin::new_unchecked(&mut e)}.resume(());
    let mut f=subslice_pattern([29u8,31,37]);let _=unsafe{Pin::new_unchecked(&mut f)}.resume(());
}

// A valid FnDef local must use the same source-type domain as capture when
// the covariance collector requests only the ordinary argument/return types.
pub fn ordinary_fn_item_local<T:Copy>(value:T)->T {
    let _function=helper::<T>;
    value
}
