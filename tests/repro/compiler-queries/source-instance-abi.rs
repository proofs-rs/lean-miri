#![no_std]

#[inline(never)]
pub fn identity<T: Copy>(value: T) -> T { value }

// A primitive result alone does not establish that raw generic arguments can
// be reified. This unused dyn argument keeps an exact material ABI residual
// while dynamic constructor reification remains outside the raw provider.
#[inline(never)]
pub fn unused<T: ?Sized>() -> u8 { 7 }

#[unsafe(no_mangle)]
pub fn source_instance_abis() {
    core::hint::black_box(identity(false));
    core::hint::black_box(identity('λ'));
    core::hint::black_box(identity(13_u8));
    core::hint::black_box(identity(-11_i16));
    core::hint::black_box(identity(73_u32));
    core::hint::black_box(identity(19_u64));
    core::hint::black_box(identity(29_u128));
    core::hint::black_box(identity(1.5_f32));
    core::hint::black_box(identity(2.5_f64));
    core::hint::black_box(identity(()));
    core::hint::black_box(unused::<dyn core::fmt::Debug>());
}
