#![no_std]
trait Generic<T> { fn generic(&self, value:T); }
trait Multi: Generic<u8> + Generic<u16> {}
fn rejected(value: &dyn Multi) { <dyn Multi as Generic<u32>>::generic(value,0); }
