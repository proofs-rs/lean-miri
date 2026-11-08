#![feature(no_core, lang_items)]
#![allow(internal_features)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u32 {}

unsafe extern "Rust" {
    fn miri_alloc(size: usize, align: usize) -> *mut u8;
}

pub unsafe fn identity(value: u32) -> u32 {
    let _ = unsafe { miri_alloc(0, 1) };
    value
}
