#![no_std]

pub struct Leaf(pub u8);

impl Drop for Leaf {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { core::ptr::write_volatile(&mut self.0, 0) }
    }
}

pub struct Outer(pub Leaf);
pub struct Empty(pub u8);

pub fn nested_late_drop() {
    let _value = Outer(Leaf(7));
}

pub unsafe fn explicit_empty_drop(pointer: *mut Empty) {
    unsafe { core::ptr::drop_in_place(pointer) }
}

pub fn direct_nontrivial_drop() {
    core::mem::drop(Leaf(9));
}
