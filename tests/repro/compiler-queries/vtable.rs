#![feature(trait_upcasting)]
#![no_std]

extern crate alloc;
use alloc::boxed::Box;

pub trait Base {
    fn base(&self) -> u8;
}

pub trait Sub: Base {
    fn sub(&self) -> u8;
}

pub struct Concrete;

impl Base for Concrete {
    fn base(&self) -> u8 { 1 }
}

impl Sub for Concrete {
    fn sub(&self) -> u8 { 2 }
}

// Direct Box<Concrete> -> Box<dyn Sub> unsizing.
#[unsafe(no_mangle)]
pub fn concrete_to_dyn() -> Box<dyn Sub> {
    Box::new(Concrete)
}

// The compiler recursively unsizes the final field through two nested ADTs.
pub struct Nested<T: ?Sized>(pub T);
pub struct Outer<T: ?Sized>(pub Nested<T>);

#[unsafe(no_mangle)]
pub fn nested_box_to_dyn() -> Box<Outer<dyn Sub>> {
    let nested: Box<Outer<Concrete>> = Box::new(Outer(Nested(Concrete)));
    nested
}

// Dynamic-to-dynamic upcast asks for the Base vtable for the concrete type
// carried by the source Box<dyn Sub> metadata.
#[unsafe(no_mangle)]
pub fn dyn_upcast(value: Box<dyn Sub>) -> Box<dyn Base> {
    value
}

// Execute a method through the destination Base vtable after the upcast.
#[unsafe(no_mangle)]
pub fn call_after_upcast(value: Box<dyn Sub>) -> u8 {
    let base: Box<dyn Base> = value;
    base.base()
}

pub struct PanicPayload(pub u8);

// This mirrors the higher-ranked callback shape used by panic hooks and keeps
// the predicate's binder in a minimal no_std crate.
pub fn box_hook<F>(hook: F) -> Box<dyn for<'a> Fn(&'a PanicPayload) + Send + Sync>
where
    F: for<'a> Fn(&'a PanicPayload) + Send + Sync + 'static,
{
    Box::new(hook)
}

fn default_hook(_: &PanicPayload) {}

#[unsafe(no_mangle)]
pub fn box_default_hook() -> Box<dyn for<'a> Fn(&'a PanicPayload) + Send + Sync> {
    box_hook(default_hook)
}

// Force a concrete indirect call through the boxed HRTB trait object.
#[unsafe(no_mangle)]
pub fn invoke_boxed_hook(payload: &PanicPayload) {
    let hook = box_default_hook();
    hook(payload)
}
