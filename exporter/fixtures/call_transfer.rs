#![no_std]
#![no_main]
#![allow(dead_code)]

use core::ffi::{c_int, c_void};

#[inline(never)]
fn pointer_target(input: *const u8) -> *mut u8 {
    input as *mut u8
}

#[inline(never)]
fn indirect_pointer_call(input: *mut u8) -> *const u8 {
    // The typed transmute keeps the call ABI-compatible while deliberately
    // making the source call operand/result types differ from the resolved
    // callee's MIR locals. The fixture is for compiler metadata export only;
    // it is never executed.
    let target: fn(*const u8) -> *mut u8 = pointer_target;
    let call: fn(*mut u8) -> *const u8 = unsafe { core::mem::transmute(target) };
    call(input)
}

trait TransferObject {
    fn get(&self, input: *mut u8) -> *const u8;
}

struct ConcreteObject;

impl TransferObject for ConcreteObject {
    #[inline(never)]
    fn get(&self, input: *mut u8) -> *const u8 {
        input as *const u8
    }
}

#[inline(never)]
fn virtual_call(object: &dyn TransferObject, input: *mut u8) -> *const u8 {
    object.get(input)
}

type ThreadStart = unsafe extern "C" fn(*mut c_void) -> *mut c_void;

unsafe extern "C" {
    fn pthread_create(
        thread: *mut usize,
        attributes: *const c_void,
        start: ThreadStart,
        argument: *mut c_void,
    ) -> c_int;
}

unsafe extern "C" fn thread_start(argument: *mut c_void) -> *mut c_void {
    argument
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_transfer_root(input: *mut u8) -> *const u8 {
    let direct_pointer = indirect_pointer_call(input);

    let concrete = ConcreteObject;
    let object: &dyn TransferObject = &concrete;
    let virtual_pointer = virtual_call(object, input);

    let mut thread = 0usize;
    let create: unsafe extern "C" fn(
        *mut usize,
        *const c_void,
        ThreadStart,
        *mut c_void,
    ) -> c_int = pthread_create;
    let _ = unsafe {
        create(
            &mut thread,
            core::ptr::null(),
            thread_start,
            input.cast(),
        )
    };

    if direct_pointer.is_null() {
        virtual_pointer
    } else {
        direct_pointer
    }
}
