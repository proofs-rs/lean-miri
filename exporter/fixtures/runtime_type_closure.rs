#![allow(dead_code)]

pub trait LateTrait {
    fn call(&self) -> u32;
}

pub struct Concrete;

// This type is used only by MIR reached through the vtable method.
pub struct LateOnly(pub u128);

pub trait InnerTrait {
    fn inner(&self) -> u32;
}

pub struct Inner;

impl InnerTrait for Inner {
    fn inner(&self) -> u32 {
        2
    }
}

#[inline(never)]
fn late_helper(value: LateOnly) -> u32 {
    value.0 as u32
}

impl LateTrait for Concrete {
    fn call(&self) -> u32 {
        let nested: &dyn InnerTrait = &Inner;
        nested.inner() + late_helper(LateOnly(17))
    }
}

pub fn make_dyn(value: &Concrete) -> &dyn LateTrait {
    value
}

pub fn call_dyn(value: &dyn LateTrait) -> u32 {
    value.call()
}
