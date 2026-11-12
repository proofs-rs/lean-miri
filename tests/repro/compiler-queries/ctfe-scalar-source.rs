#![no_std]

pub const fn arithmetic(mut n: u32) -> u32 {
    let mut sum = 0;
    while n > 0 {
        sum += n;
        n -= 1;
    }
    sum
}
