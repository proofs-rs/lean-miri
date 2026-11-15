#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]
pub fn ub() -> bool { core::intrinsics::ub_checks() }
pub fn overflow() -> bool { core::intrinsics::overflow_checks() }
