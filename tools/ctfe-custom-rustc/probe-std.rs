const fn one(n: u32) -> u32 { n + 1 }
pub struct H<const N: u32>;
impl<const N: u32> H<N> { pub const ANCHOR: u32 = one(N); }
