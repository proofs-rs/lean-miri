#![no_std]
pub struct U8<const N:u8>;
pub struct I8<const N:i8>;
pub struct Wide<const N:u128>;
pub struct Pointer<const N:usize>;
pub struct Boolean<const N:bool>;
pub fn const_name_root(_:U8<1>,_:I8<1>,_:Wide<1>,_:Pointer<1>,_:Boolean<false>) {}
