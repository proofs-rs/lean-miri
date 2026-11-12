#![allow(dead_code)]
pub struct Borrowed<'a>(pub &'a u8);
pub fn bound_function<'a:'a>() {}
pub fn fn_pointer_hashes(
 _: fn(u8)->bool,
 _: unsafe fn(*const u32)->(),
 _: extern "C" fn(i32)->i32,
 _: unsafe extern "C-unwind" fn(u8, ...)->u32,
 _: for<'a> fn(&'a u8)->&'a u8,
 _: for<'x,'y> fn(&'y u8,&'x bool)->&'y u8,
 _: for<'a> fn(for<'b> fn(&'a u8,&'b bool))->&'a u8,
 _: for<'unused,'used> fn(&'used u8),
 _: for<'a,'b> fn(for<'x> fn(&'b u8,&'a u8,&'x u8),&'a u8)->&'b u8,
 _: for<'a> fn(Borrowed<'a>)->Borrowed<'a>,
 _: fn(&'static u8)->&'static u8,
) { bound_function::<'static>(); }
