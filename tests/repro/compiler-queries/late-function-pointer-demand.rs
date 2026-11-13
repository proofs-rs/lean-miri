#![no_std]
#![allow(dead_code)]
pub fn leaf(value: u8) -> u8 { value + 1 }
pub fn make_pointer() -> fn(u8) -> u8 { leaf }
pub fn late_root() {
    // Register leaf's FnDef in the root before the later-discovered callee
    // body introduces the actual ReifyFnPointer request for that same type.
    assert_eq!(leaf(1), 2);
    let pointer = make_pointer();
    assert_eq!(pointer(2), 3);
}
pub trait Shape { fn method(&self); }
pub struct D;
impl Shape for D { fn method(&self) {} }
pub fn kcfi_impl_cast_root() { let pointer = core::hint::black_box(<D as Shape>::method as fn(&D)); pointer(&D); }
