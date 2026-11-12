#![no_std]
pub type Dynamic = for<'a> fn(&'a dyn core::fmt::Debug);
pub fn root(_value: Dynamic) {}
