#![no_std]
#[inline(never)] pub fn identity<T>(x:T)->T{x}
#[inline(never)] pub fn mutate(mut x:[u8;9])->[u8;9]{x[0]=9;x}
#[inline(never)] pub fn shared(x:[u8;9])->usize{core::hint::black_box(&x);x.len()}
#[inline(never)] pub fn capture(x:[u8;9])->*const [u8;9]{&raw const x}
#[inline(never)] pub fn residual(x:[u8;33])->[u8;33]{x}
pub fn root(){
 core::hint::black_box(identity([1u8;9]));
 core::hint::black_box(identity([1u8;16]));
 core::hint::black_box(identity([1u8;17]));
 core::hint::black_box(identity([1u8;32]));
 core::hint::black_box(identity([1i8;9]));
 core::hint::black_box(identity([true;9]));
 core::hint::black_box(identity((1u128,2u128)));
 core::hint::black_box(identity((1u128,2u64)));
 core::hint::black_box(identity((1u8,2u8,3u8,4u8,5u8,6u8,7u8,8u8,9u8)));
 core::hint::black_box(mutate([1;9]));
 core::hint::black_box(shared([1;9]));
 core::hint::black_box(capture([1;9]));
 core::hint::black_box(residual([1;33]));
}
