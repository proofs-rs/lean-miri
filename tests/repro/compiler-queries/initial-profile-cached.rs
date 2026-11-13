#![allow(dead_code)]
pub const N:usize=b"initial-snapshot".len();
pub const ASSERT_N:[u8;N]=*b"initial-snapshot";
pub static DATA:[u8;16]=*b"initial-snapshot";
pub struct Anchor;
impl Anchor {pub const VALUE:u32={let value=17u32;value};}
pub fn root()->u32 {Anchor::VALUE}
