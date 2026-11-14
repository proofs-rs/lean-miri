pub enum Void {}
pub enum Live { Value(u32), Dead(Void), DeadPair(Void,u8) }
pub enum Empty { One(Void), Two(Void,u16) }
#[repr(C,align(16))]
pub enum Aligned { Small(u8), Wide(u64,u16) }
pub enum Niche { None, Some(&'static u8) }
pub fn variant_roots(_: core::sync::atomic::Ordering, _: Live, _: Empty, _: Aligned, _: Niche, _: Void) {}
