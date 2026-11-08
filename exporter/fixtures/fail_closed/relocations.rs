#![no_std]

static VALUE: u32 = 1;
static POINTERS: [&u32; 1] = [&VALUE];

pub fn ptr() -> &'static [&'static u32] {
    &POINTERS
}
