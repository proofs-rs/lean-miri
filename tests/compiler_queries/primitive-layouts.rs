#![no_std]
#![feature(f16, f128)]

// Keep every scalar family and array constructor controls in typed MIR. The
// never-returning function pointer exports Never without running an infinite
// guest or substituting a successful no-op for divergent execution.
#[allow(clippy::type_complexity)]
pub fn primitive_layouts(
    x: (bool, char, i8, i16, i32, i64, i128, isize,
        u8, u16, u32, u64, u128, usize, f16, f32, f64, f128,
        fn(), fn() -> !, [bool; 0], [bool; 3], [(); 3], [u32; 5]),
) -> (bool, char, i8, i16, i32, i64, i128, isize,
      u8, u16, u32, u64, u128, usize, f16, f32, f64, f128,
      fn(), fn() -> !, [bool; 0], [bool; 3], [(); 3], [u32; 5]) {
    x
}
