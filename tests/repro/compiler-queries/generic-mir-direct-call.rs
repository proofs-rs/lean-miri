#![no_std]
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
