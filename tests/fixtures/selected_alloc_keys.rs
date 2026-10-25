#![allow(dead_code)]

pub trait Value {
    fn get(&self) -> u32;
}

pub struct Concrete(u32);

impl Value for Concrete {
    #[inline(never)]
    fn get(&self) -> u32 {
        self.0
    }
}

#[inline(never)]
fn increment(value: u32) -> u32 {
    value + 1
}

pub fn root(value: u32) -> u32 {
    let function: fn(u32) -> u32 = increment;
    let concrete = Concrete(function(value));
    let object: &dyn Value = &concrete;
    object.get()
}
