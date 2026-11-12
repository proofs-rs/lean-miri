#![no_std]
#![feature(auto_traits, negative_impls, unsafe_fields)]
#![allow(dead_code)]
pub unsafe auto trait Mark {}
pub struct Plain<T>(pub T);
pub struct Denied;
impl !Mark for Denied {}
pub struct UnsafeField { pub unsafe value: u8 }
pub struct Manual(pub Denied);
unsafe impl Mark for Manual {}
pub struct Recursive { pub next: *const Recursive }
pub struct RecursiveDenied { pub next: *const RecursiveDenied, pub denied: Denied }
pub fn auto_structural_root(value: Plain<u8>, _denied: Denied, _unsafe: *const UnsafeField,
    _manual: Manual, _recursive: *const Recursive, _recursive_denied: *const RecursiveDenied) -> Plain<u8> { value }
