#![no_std]
pub fn pointer_abis(
 a:fn(u8)->u8,b:fn(u16)->u16,c:fn(u32)->u32,d:fn(u64)->u64,e:fn(bool)->bool,
 f:fn(*const u8)->*const u8,g:fn(*mut u8)->*mut u8,h:fn(fn(u8)->u8)->fn(u8)->u8,
 i:for<'a>fn(&'a u8)->&'a u8,j:for<'a>fn(&'a mut u8)->&'a mut u8,
 k:fn(for<'a>fn(&'a u8)->&'a u8)->for<'a>fn(&'a u8)->&'a u8) {
 core::hint::black_box(a(1));core::hint::black_box(b(2));
 core::hint::black_box(c(3));core::hint::black_box(d(4));
 core::hint::black_box(e(true));core::hint::black_box(f(core::ptr::null()));
 core::hint::black_box(g(core::ptr::null_mut()));core::hint::black_box(h(a));
 core::hint::black_box(k(i));
 let mut x=7;core::hint::black_box(i(&x));core::hint::black_box(j(&mut x));
}
