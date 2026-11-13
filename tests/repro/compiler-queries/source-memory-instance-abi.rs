#![no_std]
#[inline(never)] pub fn identity<T>(x:T)->T{x}
#[inline(never)] pub fn residual(x:[u8;33])->[u8;33]{x}
pub fn root(){
 core::hint::black_box(identity([1u8;0]));core::hint::black_box(identity([1u8;1]));
 core::hint::black_box(identity([1u8;2]));core::hint::black_box(identity([1u8;3]));
 core::hint::black_box(identity([1u8;4]));core::hint::black_box(identity([1u8;5]));
 core::hint::black_box(identity([1u8;7]));core::hint::black_box(identity([1u8;8]));
 core::hint::black_box(identity([1i8;3]));core::hint::black_box(identity([true;3]));
 core::hint::black_box(identity((1u8,2u8,3u8)));
 core::hint::black_box(identity((true,false,true,false,true,false,true,false)));
 core::hint::black_box(residual([1;33]));
}
