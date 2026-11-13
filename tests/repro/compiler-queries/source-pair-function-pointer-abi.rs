#![no_std]
pub fn root(a:fn((bool,bool))->(bool,bool),b:fn((u8,u64))->(u8,u64),
 c:fn((u64,u8))->(u64,u8),d:fn((i16,i32))->(i16,i32),
 e:fn((u64,u64))->(u64,u64),f:fn((f32,f64))->(f32,f64),
 g:fn((char,bool))->(char,bool),h:fn((usize,isize))->(usize,isize)) {
 core::hint::black_box(a((true,false)));core::hint::black_box(b((1,2)));
 core::hint::black_box(c((1,2)));core::hint::black_box(d((1,2)));
 core::hint::black_box(e((1,2)));core::hint::black_box(f((1.,2.)));
 core::hint::black_box(g(('a',true)));core::hint::black_box(h((1,2)));
}
