#![no_std]

pub struct Deferred<T> { pub callback: fn(T) -> T, pub tail: u32 }
pub struct Novel(pub u32);

pub fn selective_material(x: Deferred<u8>, y: Novel) -> (Deferred<u8>, Novel) { (x,y) }
pub fn selective_oracle(x: *const Deferred<Novel>) -> *const Deferred<Novel> { x }
