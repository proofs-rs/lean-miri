#![no_std]
#[inline(never)] pub fn identity<T>(value:T)->T{value}
#[inline(never)] pub fn residual(value:(*const u8,u128))->(*const u8,u128){value}
#[inline(never)] pub fn reference_residual(value:(&'static u8,u64))->(&'static u8,u64){value}
#[inline(never)] pub fn fnptr_residual(value:(fn(u8)->u8,u64))->(fn(u8)->u8,u64){value}
#[inline(never)] pub fn fat_residual(value:(*const[u8],()))->(*const[u8],()){value}
fn target(x:u8)->u8{x}
static BYTE:u8=1;
pub fn root(){
 core::hint::black_box(identity((core::ptr::null::<u8>(),core::ptr::null::<u8>())));
 core::hint::black_box(identity((core::ptr::null::<u8>(),core::ptr::null_mut::<u8>())));
 core::hint::black_box(identity((core::ptr::null_mut::<bool>(),core::ptr::null_mut::<u16>())));
 core::hint::black_box(identity((core::ptr::null::<u8>(),1u64)));
 core::hint::black_box(identity((1u64,core::ptr::null::<u8>())));
 core::hint::black_box(identity((core::ptr::null_mut::<u8>(),true)));
 core::hint::black_box(identity((true,core::ptr::null_mut::<u8>())));
 core::hint::black_box(identity((core::ptr::null::<char>(),'x')));
 core::hint::black_box(identity((1i32,core::ptr::null::<u32>())));
 core::hint::black_box(identity((1f64,core::ptr::null_mut::<f32>())));
 core::hint::black_box(identity((core::ptr::null::<[u8;3]>(),1u8)));
 core::hint::black_box(identity((core::ptr::null::<fn(u8)->u8>(),1i16)));
 core::hint::black_box(residual((core::ptr::null(),1)));
 core::hint::black_box(reference_residual((&BYTE,1)));
 core::hint::black_box(fnptr_residual((target,1)));
 core::hint::black_box(fat_residual((core::ptr::slice_from_raw_parts(core::ptr::null(),0),())));
}
