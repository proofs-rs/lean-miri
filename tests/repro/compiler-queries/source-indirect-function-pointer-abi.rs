#![no_std]
pub fn root(a:fn([u8;9])->[u8;9],b:fn([u8;16])->[u8;16],c:fn([u8;17])->[u8;17],
 d:fn([u8;32])->[u8;32],e:fn([i8;9])->[i8;9],f:fn([bool;9])->[bool;9],
 g:fn((u128,u128))->(u128,u128),h:fn((u128,u64))->(u128,u64),
 i:fn((u8,u8,u8,u8,u8,u8,u8,u8,u8))->(u8,u8,u8,u8,u8,u8,u8,u8,u8),
 j:fn([u8;9])->(),k:fn()->[u8;9],l:fn([bool;17])->[bool;17]){
 core::hint::black_box(a([1;9]));core::hint::black_box(b([1;16]));
 core::hint::black_box(c([1;17]));core::hint::black_box(d([1;32]));
 core::hint::black_box(e([1;9]));core::hint::black_box(f([true;9]));
 core::hint::black_box(g((1,2)));core::hint::black_box(h((1,2)));
 core::hint::black_box(i((1,2,3,4,5,6,7,8,9)));j([1;9]);
 core::hint::black_box(k());core::hint::black_box(l([false;17]));
}
