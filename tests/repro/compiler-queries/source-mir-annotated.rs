#![allow(dead_code)]
pub fn helper<T:Copy>(value:T)->T {value}
pub fn literal<T:Copy>(value:T)->T {let _function=helper::<T>;value}
pub const fn const_literal<T:Copy>(value:T)->T {let _function=helper::<T>;value}
pub fn reify<T:Copy>(value:T)->T {let _function:fn(T)->T=helper::<T>;value}
pub fn root() {let _=literal(7u8);let _=const_literal(11u64);let _=reify(true);}
