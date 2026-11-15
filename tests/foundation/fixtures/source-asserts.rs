#![no_std]
pub fn divide(a: u8, b: u8) -> u8 { a / b }
pub fn remainder(a: u8, b: u8) -> u8 { a % b }
pub fn negate(a: i8) -> i8 { -a }
pub fn add(a: u8, b: u8) -> u8 { a + b }
pub fn bounds(a: [u8; 4], index: usize) -> u8 { a[index] }
