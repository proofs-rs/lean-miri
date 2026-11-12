#![no_std]
#![feature(allocator_api)]
extern crate alloc;
use alloc::{boxed::Box,alloc::{Allocator,AllocError,Layout}};
use core::ptr::NonNull;
#[repr(align(16))] pub struct Aligned;
pub struct Payload(pub u8);
macro_rules! allocator {($ty:ty)=>{unsafe impl Allocator for $ty {
 fn allocate(&self,_layout:Layout)->Result<NonNull<[u8]>,AllocError>{Err(AllocError)}
 unsafe fn deallocate(&self,_pointer:NonNull<u8>,_layout:Layout){}
}}}
allocator!(Aligned);allocator!(Payload);
#[inline(never)] pub fn residual_aligned(x:Box<u8,Aligned>)->Box<u8,Aligned>{x}
#[inline(never)] pub fn residual_payload(x:Box<u8,Payload>)->Box<u8,Payload>{x}
pub fn boundaries(a:Box<u8,Aligned>,b:Box<u8,Payload>){core::hint::black_box(residual_aligned(a));core::hint::black_box(residual_payload(b));}
