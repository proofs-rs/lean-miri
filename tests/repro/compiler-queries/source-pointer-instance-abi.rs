#![no_std]

#[inline(never)]
pub fn identity<T: Copy>(value: T) -> T { value }

#[inline(never)]
pub fn unused<T: ?Sized>() -> u8 { 7 }

#[inline(never)]
pub fn reference_residual(value: &'static u8) -> &'static u8 { value }

type Safe = fn(u8) -> u16;
type Unsafe = unsafe fn(u8) -> u16;
type Foreign = extern "C" fn(u8) -> u16;
type Variadic = unsafe extern "C" fn(*const u8, ...) -> u16;
type Nested = fn(Safe) -> Safe;

static DATA: u8 = 7;

// Export/oracle metadata fixture, not an execution witness. In particular the
// callers of these function-pointer arguments are outside this rooted graph.
#[unsafe(no_mangle)]
pub fn source_instance_abis(a: *const u8, b: *mut u8, c: *const u64, d: *mut (),
    e: *const *const u8, f: Safe, g: Unsafe, h: Foreign, i: Variadic, j: Nested) {
    core::hint::black_box(identity(a));
    core::hint::black_box(identity(b));
    core::hint::black_box(identity(c));
    core::hint::black_box(identity(d));
    core::hint::black_box(identity(e));
    core::hint::black_box(identity(f));
    core::hint::black_box(identity(g));
    core::hint::black_box(identity(h));
    core::hint::black_box(identity(i));
    core::hint::black_box(identity(j));
    core::hint::black_box(reference_residual(&DATA));
    core::hint::black_box(unused::<dyn core::fmt::Debug>());
}
