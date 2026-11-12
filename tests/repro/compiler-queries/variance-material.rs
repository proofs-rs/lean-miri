#![no_std]
#![allow(dead_code)]
pub struct Co<T>(pub T);
pub struct Contra<T>(pub fn(T));
pub struct Inv<T>(pub *mut T);
pub struct Nested<T>(pub Co<T>);
pub struct Phantom<T>(pub core::marker::PhantomData<T>);
pub struct Cell<T>(pub core::cell::UnsafeCell<T>);
pub struct Rec<T> { pub value: T, pub next: *const Rec<T> }
pub struct A<T> { pub value: T, pub next: *const B<T> }
pub struct B<T> { pub argument: fn(T), pub next: *const A<T> }
pub struct Const<T, const N: usize>(pub [T; N]);
pub struct Lifetime<'a, T>(pub &'a T);
pub trait Project { type Out; }
impl Project for u8 { type Out = u16; }
pub struct Projection<T: Project>(pub T::Out);
pub type Alias<T> = *const T;
pub struct AliasCo<T>(pub Alias<T>);
pub fn unused<T>() {}
pub fn identity<T>(value: T) -> T { value }
pub fn variance_root(_a: Co<u8>, _b: Contra<u8>, _c: Inv<u8>, _d: Nested<u8>,
    _e: Phantom<u8>, _f: Cell<u8>, _g: Rec<u8>, _h: A<u8>, _i: B<u8>,
    _j: Const<u8, 7>, _k: Lifetime<'static, u8>, _l: Projection<u8>, _m: AliasCo<u8>) {
    unused::<u8>();
    let _ = identity(7_u8);
}
