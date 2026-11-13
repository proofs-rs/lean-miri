#![no_std]
pub const fn arithmetic(mut n:u32)->u32 {
 let mut sum=0;
 while n>0 {sum+=n;n-=1;}
 sum
}
pub struct Holder<const N:u32>;
impl<const N:u32> Holder<N> {
 pub const ROOT:u32=arithmetic(N);
 pub const SAME:u32=arithmetic(N);
}
