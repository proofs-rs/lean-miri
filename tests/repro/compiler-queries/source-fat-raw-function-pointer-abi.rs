#![no_std]
pub fn root(f0:fn(*const [u8])->*const [u8],x0:*const [u8],f1:fn(*mut [u8])->*mut [u8],x1:*mut [u8],f2:fn(*const [u64])->*const [u64],x2:*const [u64],f3:fn(*mut [u64])->*mut [u64],x3:*mut [u64],f4:fn(*const [u128])->*const [u128],x4:*const [u128],f5:fn(*mut [bool])->*mut [bool],x5:*mut [bool],f6:fn(*const [[u8;3]])->*const [[u8;3]],x6:*const [[u8;3]],f7:fn(*mut [()])->*mut [()],x7:*mut [()],f8:fn(*const [*const u8])->*const [*const u8],x8:*const [*const u8],f9:fn(*mut [fn(u8)->u8])->*mut [fn(u8)->u8],x9:*mut [fn(u8)->u8],f10:fn(*const str)->*const str,x10:*const str,f11:fn(*mut str)->*mut str,x11:*mut str){
 core::hint::black_box(f0(x0));
 core::hint::black_box(f1(x1));
 core::hint::black_box(f2(x2));
 core::hint::black_box(f3(x3));
 core::hint::black_box(f4(x4));
 core::hint::black_box(f5(x5));
 core::hint::black_box(f6(x6));
 core::hint::black_box(f7(x7));
 core::hint::black_box(f8(x8));
 core::hint::black_box(f9(x9));
 core::hint::black_box(f10(x10));
 core::hint::black_box(f11(x11));
}
