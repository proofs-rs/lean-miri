#![no_std]
trait ConstObject { const N:usize; fn method(&self); }
fn rejected(_: &dyn ConstObject) {}
