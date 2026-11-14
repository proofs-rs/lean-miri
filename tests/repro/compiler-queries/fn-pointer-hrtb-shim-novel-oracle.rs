#![feature(fn_static)]
#![no_std]
// Independent compiler bodies for the safety-flipped types constructed outside
// the production export's material prefix.
pub type H0 = for<'a> fn(&'a u8) -> &'a u8;
pub type H1 = for<'a, 'b> unsafe fn(&'b u16, &'a [u8]) -> u32;
pub type H2 = for<'a> extern "C" fn(&'a u32) -> usize;
pub type H3 = for<'a> unsafe extern "C" fn(&'a u32, ...) -> usize;
pub type H4 = for<'a> unsafe fn(&'a u8) -> &'a u8;
pub type H5 = for<'a, 'b> fn(&'b u16, &'a [u8]) -> u32;
pub type H6 = for<'a> unsafe extern "C" fn(&'a u32) -> usize;
pub type H7 = for<'a> extern "C" fn(&'a u32, ...) -> usize;
