#![no_std]
pub fn root(a:fn([u8;0])->[u8;0],b:fn([u8;1])->[u8;1],c:fn([u8;2])->[u8;2],d:fn([u8;3])->[u8;3],
 e:fn([u8;4])->[u8;4],f:fn([u8;5])->[u8;5],g:fn([u8;7])->[u8;7],h:fn([u8;8])->[u8;8],
 i:fn([i8;3])->[i8;3],j:fn([bool;3])->[bool;3],k:fn((u8,u8,u8))->(u8,u8,u8),
 l:fn((bool,bool,bool,bool,bool,bool,bool,bool))->(bool,bool,bool,bool,bool,bool,bool,bool)){
 core::hint::black_box(a([1;0]));core::hint::black_box(b([1;1]));core::hint::black_box(c([1;2]));
 core::hint::black_box(d([1;3]));core::hint::black_box(e([1;4]));core::hint::black_box(f([1;5]));
 core::hint::black_box(g([1;7]));core::hint::black_box(h([1;8]));core::hint::black_box(i([1;3]));
 core::hint::black_box(j([true;3]));core::hint::black_box(k((1,2,3)));
 core::hint::black_box(l((true,false,true,false,true,false,true,false)));
}
