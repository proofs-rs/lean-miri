#![no_std]
pub fn marker<const N:u8>() {}
pub fn constant_root() { marker::<1>(); }
