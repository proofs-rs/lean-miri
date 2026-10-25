#![feature(explicit_tail_calls)]
#[inline(never)]
pub fn leaf(value: u32) -> u32 { value + 1 }
#[inline(never)]
pub fn generic_id<T>(value: T) -> T { value }
#[inline(never)]
pub fn nested(value: u32) -> u32 { generic_id::<u32>(leaf(value)) }
pub fn root(value: u32) -> u32 { nested(value) }
#[inline(never)]
pub fn tail_bridge(value: u32) -> u32 { become leaf(value) }
pub fn tail_root(value: u32) -> u32 { tail_bridge(value) }
pub fn overflow_root(value: u32) -> u32 { leaf(value) }
