#![no_std]

pub const fn arithmetic(mut n: u32) -> u32 {
    let mut sum = 0;
    while n > 0 {
        sum += n;
        n -= 1;
    }
    sum
}

pub const INPUT: u32 = 9;
pub const ROOT: u32 = arithmetic(INPUT);

// This declaration must never be loaded with mir_for_ctfe as though it had a body.
pub trait RequiredSource {
    const VALUE: u32;
}
