#![no_std]
const fn divide(n:u32)->u32 {1/n}
pub trait Source {const VALUE:u32;}
pub struct Good;
pub struct Bad;
impl Source for Good {const VALUE:u32=7;}
impl Source for Bad {const VALUE:u32=divide(0);}
pub const fn callee<T:Source>(n:u32)->u32 {n+T::VALUE}
