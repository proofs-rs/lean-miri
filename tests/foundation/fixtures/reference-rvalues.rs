pub fn reborrow(value: &'static u8) -> &'static u8 { &*value }
