#![no_std]
#[inline(never)] pub fn identity<T>(value:T)->T{value}
#[inline(never)] pub fn residual(value:(*const u8,u128))->(*const u8,u128){value}
#[inline(never)] pub fn reference_residual(value:(&'static u8,u64))->(&'static u8,u64){value}
#[inline(never)] pub fn fnptr_residual(value:(fn(u8)->u8,u64))->(fn(u8)->u8,u64){value}
#[inline(never)] pub fn fat_residual(value:(*const[u8],()))->(*const[u8],()){value}
#[inline(never)] pub fn fat_reference_residual(value:&'static[u8])->&'static[u8]{value}
fn target(x:u8)->u8{x}
static BYTE:u8=1;
pub fn root(x0:*const [u8],x1:*mut [u8],x2:*const [u64],x3:*mut [u64],x4:*const [u128],x5:*mut [bool],x6:*const [[u8;3]],x7:*mut [()],x8:*const [*const u8],x9:*mut [fn(u8)->u8],x10:*const str,x11:*mut str){
 core::hint::black_box(identity(x0));
 core::hint::black_box(identity(x1));
 core::hint::black_box(identity(x2));
 core::hint::black_box(identity(x3));
 core::hint::black_box(identity(x4));
 core::hint::black_box(identity(x5));
 core::hint::black_box(identity(x6));
 core::hint::black_box(identity(x7));
 core::hint::black_box(identity(x8));
 core::hint::black_box(identity(x9));
 core::hint::black_box(identity(x10));
 core::hint::black_box(identity(x11));
 core::hint::black_box(residual((core::ptr::null(),1)));
 core::hint::black_box(reference_residual((&BYTE,1)));
 core::hint::black_box(fnptr_residual((target,1)));
 core::hint::black_box(fat_residual((core::ptr::slice_from_raw_parts(core::ptr::null(),0),())));
 core::hint::black_box(fat_reference_residual(&[]));
}
