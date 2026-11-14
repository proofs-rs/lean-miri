#![no_std]
#![no_main]
#![feature(adt_const_params)]
use core::marker::ConstParamTy;

#[derive(PartialEq, Eq, ConstParamTy)]
pub struct Empty;
#[repr(align(16))]
#[derive(PartialEq, Eq, ConstParamTy)]
pub struct Aligned;
#[repr(transparent)]
#[derive(PartialEq, Eq, ConstParamTy)]
pub struct Wrapper(pub u32);
#[repr(transparent)]
#[derive(PartialEq, Eq, ConstParamTy)]
pub struct Nested(pub Wrapper);
#[repr(C)]
#[derive(PartialEq, Eq, ConstParamTy)]
pub struct CWrapper(pub u32);

#[inline(never)] fn unit<const V: ()>() { V }
#[inline(never)] fn empty_array<const V: [u8; 0]>() -> [u8; 0] { V }
#[inline(never)] fn unit_array<const V: [(); 3]>() -> [(); 3] { V }
#[inline(never)] fn empty_struct<const V: Empty>() -> Empty { V }
#[inline(never)] fn aligned_struct<const V: Aligned>() -> Aligned { V }
#[inline(never)] fn scalar_tuple<const V: (u32,)>() -> (u32,) { V }
#[inline(never)] fn scalar_wrapper<const V: Wrapper>() -> Wrapper { V }
#[inline(never)] fn scalar_nested<const V: Nested>() -> Nested { V }
#[inline(never)] fn scalar_tuple_nested<const V: ((u32,),)>() -> ((u32,),) { V }
#[inline(never)] fn zero_nested<const V: (Aligned, [u8; 0])>() -> (Aligned, [u8; 0]) { V }
#[inline(never)] fn residual_pair<const V: (u8, u16)>() -> (u8, u16) { V }
#[inline(never)] fn residual_c<const V: CWrapper>() -> CWrapper { V }

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    unit::<{ () }>();
    let a = empty_array::<{ [] }>();
    let b = unit_array::<{ [(); 3] }>();
    let _ = empty_struct::<{ Empty }>();
    let _ = aligned_struct::<{ Aligned }>();
    let _ = zero_nested::<{ (Aligned, []) }>();
    if a.len() == 0 && b.len() == 3 && scalar_tuple::<{ (37,) }>().0 == 37 &&
        scalar_wrapper::<{ Wrapper(73) }>().0 == 73 &&
        scalar_nested::<{ Nested(Wrapper(109)) }>().0.0 == 109 &&
        scalar_tuple_nested::<{ ((149,),) }>().0.0 == 149 &&
        residual_pair::<{ (3, 257) }>() == (3, 257) &&
        residual_c::<{ CWrapper(181) }>().0 == 181 { 0 } else { 1 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
