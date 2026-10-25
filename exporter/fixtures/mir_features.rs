#![allow(dead_code)]
#![feature(thread_local)]

use core::sync::atomic::{AtomicUsize, Ordering};

#[repr(C)]
pub union WordOrFloat {
    pub word: u32,
    pub float: f32,
}

#[repr(u8)]
pub enum DirectTag {
    Zero = 0,
    One = 1,
}

pub fn direct_tag_value(tag: DirectTag) -> u8 {
    match tag {
        DirectTag::Zero => 0,
        DirectTag::One => 1,
    }
}

pub trait ValueSource {
    fn get(&self) -> u32;
}

pub struct ValueCell(pub u32);

impl ValueSource for ValueCell {
    fn get(&self) -> u32 {
        self.0
    }
}

// Keep a concrete vtable allocation in the unscoped exporter fixture so the
// decoder's vtable-entry assertion exercises actual compiler output.
pub static VTABLE_ROOT: &(dyn ValueSource + Sync) = &ValueCell(23);

pub fn get_vtable_root() -> &'static (dyn ValueSource + Sync) {
    VTABLE_ROOT
}

pub struct DropValue(pub u32);

impl Drop for DropValue {
    fn drop(&mut self) {}
}

impl ValueSource for DropValue {
    fn get(&self) -> u32 {
        self.0
    }
}

pub fn as_trait_object(value: &ValueCell) -> &dyn ValueSource {
    value
}

pub fn as_drop_trait_object(value: &DropValue) -> &dyn ValueSource {
    value
}

pub fn call_trait_object(value: &dyn ValueSource) -> u32 {
    value.get()
}

pub struct Link<T> {
    pub next: Option<Box<Link<T>>>,
    pub value: T,
}

pub fn make_link(value: u32) -> Link<u32> {
    Link { next: None, value }
}

pub fn promoted_ref() -> &'static u32 {
    &42
}

pub fn byte_string() -> &'static [u8] {
    b"lean-miri"
}

pub fn pointer_slice() -> &'static [&'static u32] {
    &[&42, &7]
}

pub static STATIC_DATA: [u32; 2] = [11, 13];

#[thread_local]
pub static TLS_WORD: u32 = 17;

pub const STATIC_REF: &'static [u32; 2] = &STATIC_DATA;

pub fn read_tls() -> u32 {
    TLS_WORD
}

pub fn id<T>(value: T) -> T {
    value
}

pub fn array_len<const N: usize>() -> [u8; N] {
    [0; N]
}

pub fn exercise(pointer: *mut u32, atom: &AtomicUsize, input: u32) -> u32 {
    let _inverse = !input;
    let _address = pointer as usize;
    let mut sum = 0;
    let mut index = 0;
    while index < input {
        sum += index;
        index += 1;
    }
    let union = WordOrFloat { word: sum };
    let loaded = unsafe { *pointer };
    let _old = atom.fetch_add(1, Ordering::SeqCst);
    let _sized = array_len::<3>();
    id(loaded.wrapping_add(unsafe { union.word }))
}
