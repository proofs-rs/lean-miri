#![no_std]
pub const INPUT:u32=9;
pub const fn arithmetic(mut n:u32)->u32 {let mut sum=0;while n>0 {sum+=n;n-=1;}sum}
pub const fn root_call()->u32 {arithmetic(INPUT)}
pub const ROOT:u32=arithmetic(INPUT);
