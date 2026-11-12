#![no_std]
pub struct Wrap<T>(pub T);
pub fn identity<T>(value: T) -> T { value }
pub unsafe fn unsafe_identity<T>(value: T) -> T { value }
#[target_feature(enable = "sse2")]
pub fn feature_identity<T>(value: T) -> T { value }
pub fn noop<T>() {}
pub mod nested { pub fn identity<T>(value:T)->T { value } }
pub fn function_name_root(value:Wrap<u8>) -> Wrap<u8> {
    noop::<u8>();
    let value = identity(value);
    let value = unsafe { unsafe_identity(value) };
    let value = unsafe { feature_identity(value) };
    nested::identity(value)
}
