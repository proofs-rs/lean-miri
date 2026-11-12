#![no_std]
#![feature(unboxed_closures, fn_traits)]
#![allow(non_snake_case)]
#[inline(never)] pub fn GenericMirIdentity<T: Copy>(value: T) -> T { value }
#[inline(never)] pub fn GenericMirPair<T: Copy, U: Copy>(left: T, right: U) -> (T, U) { (left, right) }
#[inline(never)] pub fn GenericMirArray<T: Copy>(left: T, right: T) -> [T; 2] { [left, right] }
#[inline(never)] pub fn GenericMirConstIdentity<T: Copy, const N: usize>(value: [T; N]) -> [T; N] { value }

#[inline(never)] pub fn ResidualMirProjected<T: Copy>(value: (T, T)) -> T { value.0 }
#[inline(never)] pub fn ResidualMirConstant<T: Copy>(value: T) -> (T, u32) { (value, 5) }
#[inline(never)] pub fn ResidualMirDrop<T>(value: T) { core::mem::drop(value) }
#[inline(never)] pub fn ResidualMirFnPtr<T: Copy>(value: fn(T) -> T) -> fn(T) -> T { value }
#[inline(never)] pub fn GenericMirChoice<T: Copy>(condition: bool, left: T, right: T) -> T {
    if condition { left } else { right }
}

#[inline(never)] pub extern "rust-call" fn GenericMirRustCall<T: Copy>(args: (T,)) -> (T,) { args }
