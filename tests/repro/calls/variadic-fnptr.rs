#![no_std]
#![no_main]
#![allow(dead_code)]

unsafe extern "C" {
    fn variadic_probe(fixed: i32, ...) -> i32;
}

#[inline(never)]
fn unrelated_nonvariadic(value: i32) -> i32 {
    value
}

// The exporter scans function-pointer allocations, while the explicit cast in
// the exported root below also keeps this ordinary target present in MIR.
#[used]
static UNRELATED_TARGET: fn(i32) -> i32 = unrelated_nonvariadic;

// Exporter entry root: this is a no_std library and is not linked or run. The
// call exists to make rustc emit the indirect variadic FnPtr call in MIR.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn variadic_callsite() -> i32 {
    let _candidate: fn(i32) -> i32 = unrelated_nonvariadic as fn(i32) -> i32;
    let callee: unsafe extern "C" fn(i32, ...) -> i32 = variadic_probe;
    unsafe { callee(7, 11i32) }
}
