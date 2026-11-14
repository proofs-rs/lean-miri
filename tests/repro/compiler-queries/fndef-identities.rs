#![no_std]

// Identical instantiated signatures retain different physical FnDef identities.
#[inline(never)]
fn first<T>(value: T) -> T { value }
#[inline(never)]
fn second<T>(value: T) -> T { value }

// Its late-bound signature region is independent of the FnDef argument binder.
#[inline(never)]
fn from_ref(value: &u32) -> u32 { *value }

pub fn root(value: u32) -> u32 { second(first(from_ref(&value))) }
