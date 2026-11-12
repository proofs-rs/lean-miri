#![no_std]
#![no_main]

use core::mem::{ManuallyDrop, MaybeUninit};

struct Droppy(*mut u32);
impl Drop for Droppy {
    fn drop(&mut self) { unsafe { *self.0 += 1; } }
}
struct Plain<T>(T);

// These checks may be folded by rustc. Query-algorithm correspondence is tested
// independently by CompareNeedsDrop; this guest checks observable drop behavior.
#[inline(never)]
fn expected_needs_drop<T>() -> bool { core::mem::needs_drop::<T>() }
#[inline(never)]
fn expected_needs_drop_of<T>(_: &T) -> bool { expected_needs_drop::<T>() }

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    if expected_needs_drop::<u32>()
        || !expected_needs_drop::<Droppy>()
        || !expected_needs_drop::<Plain<Droppy>>()
        || expected_needs_drop::<[Droppy; 0]>()
        || !expected_needs_drop::<[Droppy; 2]>()
        || expected_needs_drop::<ManuallyDrop<Droppy>>()
        || expected_needs_drop::<MaybeUninit<Droppy>>() { return 1; }
    let mut count = 0u32;
    let pointer = &mut count as *mut u32;
    let _manual = ManuallyDrop::new(Droppy(pointer));
    let _uninitialized = MaybeUninit::new(Droppy(pointer));
    let zero: [Droppy; 0] = [];
    drop(zero);
    drop([Droppy(pointer), Droppy(pointer)]);
    drop(Plain(Droppy(pointer)));
    let captured = Droppy(pointer);
    let closure = move || drop(captured);
    if !expected_needs_drop_of(&closure) { return 2; }
    drop(closure);
    if count == 4 { 0 } else { 3 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
