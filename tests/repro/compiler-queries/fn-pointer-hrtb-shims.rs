#![feature(fn_static)]
#![no_std]
use core::ops::FnPtr;
pub type H0 = for<'a> fn(&'a u8) -> &'a u8;
pub type H1 = for<'a,'b> unsafe fn(&'b u16,&'a [u8]) -> u32;
pub type H2 = for<'a> extern "C" fn(&'a u32) -> usize;
pub type H3 = for<'a> unsafe extern "C" fn(&'a u32,...) -> usize;
pub fn roundtrip(a:H0,b:H1,c:H2,d:H3)->(H0,H1,H2,H3) {
 unsafe {(H0::from_ptr(a.as_ptr()),H1::from_ptr(b.as_ptr()),H2::from_ptr(c.as_ptr()),H3::from_ptr(d.as_ptr()))}
}
