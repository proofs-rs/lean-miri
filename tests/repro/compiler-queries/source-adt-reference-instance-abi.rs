#![no_std]
use core::{cell::UnsafeCell,marker::PhantomPinned};
#[repr(transparent)] pub struct Plain(pub u8);
#[repr(transparent)] pub struct NoFreeze(pub UnsafeCell<u8>);
#[repr(C)] pub struct NoUnpin(pub u8,pub PhantomPinned);
#[inline(never)] pub fn identity<T>(x:T)->T{x}
#[inline(never)] pub fn unused<T:?Sized>()->u8{7}
#[inline(never)] pub fn reference_residual(x:&'static[u8])->&'static[u8]{x}
static DATA:u8=7;
pub fn source_instance_abis(a:&Plain,b:&mut Plain,c:&NoFreeze,d:&mut NoFreeze,e:&NoUnpin,f:&mut NoUnpin,g:&[u8;13],h:&mut[u8;13],i:&(u8,u64),j:&mut(u8,u64)) {
 core::hint::black_box(identity(a));core::hint::black_box(identity(b));
 core::hint::black_box(identity(c));core::hint::black_box(identity(d));
 core::hint::black_box(identity(e));core::hint::black_box(identity(f));
 core::hint::black_box(identity(g));core::hint::black_box(identity(h));
 core::hint::black_box(identity(i));core::hint::black_box(identity(j));
 core::hint::black_box(reference_residual(core::slice::from_ref(&DATA)));
 core::hint::black_box(unused::<dyn core::fmt::Debug>());
}
