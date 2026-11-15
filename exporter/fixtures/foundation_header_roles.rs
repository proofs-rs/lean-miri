#![feature(intrinsics)]
#![allow(internal_features)]
#[rustc_intrinsic]
pub fn breakpoint();
pub fn ordinary() {}
fn main() {}
