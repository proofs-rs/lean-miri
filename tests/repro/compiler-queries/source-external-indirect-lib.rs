#![no_std]
#[inline(never)] pub fn identity<T>(value:T)->T{value}
#[inline(never)] pub fn accept_pair(_value:(u128,u128))->u8{1}
