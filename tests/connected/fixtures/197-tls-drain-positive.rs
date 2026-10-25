#![no_std]
#![no_main]

use core::ffi::c_void;

extern crate libc;

static mut KEY_B: libc::pthread_key_t = 0;
static mut KEY_A: libc::pthread_key_t = 0;
static mut TOKEN_A: u8 = 0xA1;
static mut TOKEN_B: u8 = 0xB2;
static mut COUNT: u32 = 0;
static mut FAILURE: u32 = 0;

unsafe extern "C" fn destructor_b(value: *mut c_void) {
    unsafe {
        if value != core::ptr::addr_of_mut!(TOKEN_B).cast::<c_void>() {
            core::ptr::write_volatile(core::ptr::addr_of_mut!(FAILURE), 1);
            return;
        }
        let count = core::ptr::read_volatile(core::ptr::addr_of!(COUNT));
        core::ptr::write_volatile(core::ptr::addr_of_mut!(COUNT), count + 1);
    }
}

unsafe extern "C" fn destructor_a(value: *mut c_void) {
    unsafe {
        if value != core::ptr::addr_of_mut!(TOKEN_A).cast::<c_void>() {
            core::ptr::write_volatile(core::ptr::addr_of_mut!(FAILURE), 1);
            return;
        }
        let count = core::ptr::read_volatile(core::ptr::addr_of!(COUNT));
        core::ptr::write_volatile(core::ptr::addr_of_mut!(COUNT), count + 1);
        if libc::pthread_setspecific(
            KEY_B,
            core::ptr::addr_of_mut!(TOKEN_B).cast::<c_void>(),
        ) != 0
        {
            core::ptr::write_volatile(core::ptr::addr_of_mut!(FAILURE), 2);
        }
    }
}

extern "C" fn child_entry(_: *mut c_void) -> *mut c_void {
    unsafe {
        if libc::pthread_setspecific(
            KEY_A,
            core::ptr::addr_of_mut!(TOKEN_A).cast::<c_void>(),
        ) != 0
        {
            core::ptr::write_volatile(core::ptr::addr_of_mut!(FAILURE), 3);
        }
    }
    core::ptr::null_mut()
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        let mut key_b: libc::pthread_key_t = 0;
        if libc::pthread_key_create(&mut key_b, Some(destructor_b)) != 0 {
            return 1;
        }
        KEY_B = key_b;

        let mut key_a: libc::pthread_key_t = 0;
        if libc::pthread_key_create(&mut key_a, Some(destructor_a)) != 0 {
            return 2;
        }
        KEY_A = key_a;

        let mut child: libc::pthread_t = 0;
        if libc::pthread_create(&mut child, core::ptr::null(), child_entry, core::ptr::null_mut()) != 0 {
            return 3;
        }
        if libc::pthread_join(child, core::ptr::null_mut()) != 0 {
            return 4;
        }

        if core::ptr::read_volatile(core::ptr::addr_of!(FAILURE)) != 0 {
            return 5;
        }
        if core::ptr::read_volatile(core::ptr::addr_of!(COUNT)) != 2 {
            return 6;
        }
    }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
