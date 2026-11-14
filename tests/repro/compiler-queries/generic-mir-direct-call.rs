#![no_std]
#![feature(core_intrinsics,c_variadic)]
#![allow(non_snake_case)]

#[inline(never)]
pub fn leaf<T: Copy>(value: T) -> T { value }

#[inline(never)]
pub fn GenericDirectCall<T: Copy>(value: T) -> T { leaf(value) }

#[inline(never)]
pub fn leaf_pair<T: Copy, U: Copy>(left: T, right: U) -> (T, U) { (left, right) }

#[inline(never)]
pub fn GenericDirectPair<T: Copy, U: Copy>(left: T, right: U) -> (T, U) {
    leaf_pair(left, right)
}

pub fn ResidualDirectPointer<T: Copy>(function: fn(T) -> T, value: T) -> T {
    function(value)
}

pub fn ResidualDirectTrait<T: Copy + Clone>(value: T) -> T { value.clone() }


pub fn ResidualDirectIntrinsic<T: Copy>(value: T) -> T {
    core::intrinsics::black_box(value)
}

unsafe extern "C" { fn foreign_source_call(value: u32) -> u32; }
pub fn ResidualDirectForeign(value: u32) -> u32 {
    unsafe { foreign_source_call(value) }
}

unsafe extern "C" fn variadic_source_call(value: u32, _: ...) -> u32 { value }
pub fn ResidualDirectVariadic(value: u32) -> u32 {
    unsafe { variadic_source_call(value, value) }
}
