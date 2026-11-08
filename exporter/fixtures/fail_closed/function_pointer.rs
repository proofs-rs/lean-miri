#![no_std]

fn target(value: u32) -> u32 { value }

pub fn identity(value: u32) -> u32 {
    let function: fn(u32) -> u32 = target;
    function(value)
}
