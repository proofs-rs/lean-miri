#![feature(trait_upcasting)]
#![no_std]

pub trait Base {
    fn base(&self) -> u8;
}

pub trait Sub: Base {
    fn sub(&self) -> u8;
}

pub fn upcast(value: &dyn Sub) -> &dyn Base {
    value
}
