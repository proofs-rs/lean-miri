#![feature(unboxed_closures, fn_traits)]
#![no_std]
#[inline(never)]
pub extern "rust-call" fn pair(args: (u8, u16)) -> u32 { args.0 as u32 + args.1 as u32 }
pub struct S(u32);
impl S {
#[inline(never)]
pub extern "rust-call" fn prefix(self, args: (u8, u16)) -> u32 { self.0 + pair(args) }
}
#[track_caller]
#[inline(never)]
pub fn tracked(value: u32) -> u32 { value + 1 }
unsafe extern "C" { fn variadic(value: u32, ...) -> u32; }
#[inline(never)]
pub unsafe fn root() -> u32 { S(tracked(1)).prefix((2, 3)) + unsafe { variadic(4, 5_u32, 6_f64) } }
