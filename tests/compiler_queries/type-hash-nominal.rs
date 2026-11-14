#![allow(dead_code)]
#![feature(adt_const_params)]
#[derive(Clone)] pub struct Named<T> { pub x: T }
pub struct Tuple<T>(pub T);
pub enum Choice<T> { A, B(T), C{x:T} }
pub struct Borrowed<'a,T> { pub value: &'a T }
#[repr(C,align(16))] pub struct Aligned { pub x:u8 }
#[repr(packed(2))] pub struct Packed { pub x:u32, pub y:u8 }
#[repr(i16)] pub enum Explicit { A=-2, B, C=257 }
pub union Bits { pub x:u32, pub y:f32 }
pub struct Empty;
pub enum Never {}
pub fn plain() {}
pub fn generic<T>() {}
pub struct Consty<const N:usize>;
pub struct Flags<const B:bool>;
pub struct Aggregate<const V:(u8,bool)>;
pub fn nominal_hashes(_:Consty<7>, _:Flags<true>, _:[u8;3], _:Named<u32>, _:Named<&'static u8>, _:Tuple<(u8,bool)>, _:Choice<u16>, _:Borrowed<'static,u64>, _:Aligned, _:Packed, _:Explicit, _:Bits, _:Empty, _:Never) { plain(); generic::<u32>(); }
