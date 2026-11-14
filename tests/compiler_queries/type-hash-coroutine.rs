#![no_std]
#![allow(dead_code)]
pub fn generic_hashes<T: Copy>(value:T) -> impl core::future::Future<Output=T> { async move {value} }
pub fn coroutine_hashes(value:u32, borrowed:&'static u16) -> (impl core::future::Future<Output=u8>,impl core::future::Future<Output=u32>,impl core::future::Future<Output=u16>,impl core::future::Future<Output=u16>) {
 (async {17u8},async move {value},async move {*borrowed},generic_hashes(7u16))
}
