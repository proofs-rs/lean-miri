#![no_std]
#![feature(allocator_api)]
extern crate alloc;
use alloc::alloc::{Allocator,AllocError,Layout};
use alloc::boxed::Box;
use core::{ptr::NonNull,marker::PhantomPinned,cell::UnsafeCell};
// The local name deliberately collides with alloc::alloc::Global. No lang item.
pub struct Global;
unsafe impl Allocator for Global {
 fn allocate(&self,_layout:Layout)->Result<NonNull<[u8]>,AllocError>{Err(AllocError)}
 unsafe fn deallocate(&self,_pointer:NonNull<u8>,_layout:Layout){}
}
#[repr(transparent)] pub struct Plain(pub u8);
#[repr(C)] pub struct Pinned(pub u8,pub PhantomPinned);
#[inline(never)] pub fn identity<T>(value:T)->T{value}
pub fn source_instance_abis(a:Box<u8>,b:Box<u64>,c:Box<()>,d:Box<[u8;13]>,e:Box<u128>,
 f:Box<Pinned>,g:Box<UnsafeCell<u8>>,h:Box<u8,Global>,i:Box<u64,Global>,j:Box<(),Global>,k:Box<[u8]>){
 core::hint::black_box(identity(a));core::hint::black_box(identity(b));
 core::hint::black_box(identity(c));core::hint::black_box(identity(d));
 core::hint::black_box(identity(e));core::hint::black_box(identity(f));
 core::hint::black_box(identity(g));core::hint::black_box(identity(h));
 core::hint::black_box(identity(i));core::hint::black_box(identity(j));
 core::hint::black_box(residual(k));
}

#[inline(never)] pub fn residual(value:Box<[u8]>)->Box<[u8]>{value}
