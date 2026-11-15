#![no_std]
#![crate_type = "lib"]

pub fn use_closure(function: fn() -> i32) -> i32 {
    let closure = move || function();
    let object: &dyn Fn() -> i32 = &closure;
    object()
}
