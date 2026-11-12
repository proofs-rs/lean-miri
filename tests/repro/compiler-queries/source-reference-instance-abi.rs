#![no_std]

#[inline(never)]
pub fn identity<T>(value: T) -> T { value }

#[inline(never)]
pub fn unused<T: ?Sized>() -> u8 { 7 }

#[inline(never)]
pub fn reference_residual(value: &'static [u8]) -> &'static [u8] { value }

static DATA: u8 = 7;

// Metadata/oracle fixture. Arguments are not dereferenced or executed here.
#[unsafe(no_mangle)]
pub fn source_instance_abis(a: &'static u8, b: &'static mut u8,
    c: &'static u64, d: &'static mut u64, e: &'static (), f: &'static mut (),
    g: &'static *const u8, h: &'static mut *mut u8,
    i: &'static fn(u8) -> u16, j: &'static mut fn(u8) -> u16) {
    core::hint::black_box(identity(a));
    core::hint::black_box(identity(b));
    core::hint::black_box(identity(c));
    core::hint::black_box(identity(d));
    core::hint::black_box(identity(e));
    core::hint::black_box(identity(f));
    core::hint::black_box(identity(g));
    core::hint::black_box(identity(h));
    core::hint::black_box(identity(i));
    core::hint::black_box(identity(j));
    core::hint::black_box(reference_residual(core::slice::from_ref(&DATA)));
    core::hint::black_box(unused::<dyn core::fmt::Debug>());
}
