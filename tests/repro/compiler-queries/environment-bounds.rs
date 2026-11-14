#![no_std]
#![allow(dead_code)]
pub trait Super: Sized {}
impl Super for u8 {}
pub struct Direct<T: Sized> { pub value: T }
pub struct Inherited<T: ?Sized + Super> { pub value: T }
pub struct Maybe<T: ?Sized> { pub value: T }
pub fn environment_bounds_root(a: Direct<u8>, b: Inherited<u8>, _c: *const Maybe<[u8]>)
    -> (Direct<u8>,Inherited<u8>) { (a,b) }
