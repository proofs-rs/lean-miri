#![no_std]
#![feature(allocator_api)]
extern crate alloc;
use alloc::{boxed::Box,alloc::{Allocator,AllocError,Layout}};
use core::ptr::NonNull;
pub struct Global;
unsafe impl Allocator for Global {
 fn allocate(&self,_layout:Layout)->Result<NonNull<[u8]>,AllocError>{Err(AllocError)}
 unsafe fn deallocate(&self,_pointer:NonNull<u8>,_layout:Layout){}
}
#[inline(never)] pub fn identity<T>(x:T)->T{x}
pub fn base(a:Box<()>,b:Box<(),Global>)->(Box<()>,Box<(),Global>){(identity(a),identity(b))}
pub fn oracle_global(x:Box<[u8;13]>)->Box<[u8;13]>{identity(x)}
pub fn oracle_custom(x:Box<[u8;13],Global>)->Box<[u8;13],Global>{identity(x)}
