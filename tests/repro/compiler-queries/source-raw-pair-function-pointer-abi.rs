#![no_std]
pub fn root(a:fn((*const u8,*const u8))->(*const u8,*const u8),
 b:fn((*const u8,*mut u8))->(*const u8,*mut u8),
 c:fn((*mut bool,*mut u16))->(*mut bool,*mut u16),
 d:fn((*const u8,u64))->(*const u8,u64),e:fn((u64,*const u8))->(u64,*const u8),
 f:fn((*mut u8,bool))->(*mut u8,bool),g:fn((bool,*mut u8))->(bool,*mut u8),
 h:fn((*const char,char))->(*const char,char),i:fn((i32,*const u32))->(i32,*const u32),
 j:fn((f64,*mut f32))->(f64,*mut f32),k:fn((*const [u8;3],u8))->(*const [u8;3],u8),
 l:fn((*const fn(u8)->u8,i16))->(*const fn(u8)->u8,i16)){
 core::hint::black_box(a((core::ptr::null(),core::ptr::null())));
 core::hint::black_box(b((core::ptr::null(),core::ptr::null_mut())));
 core::hint::black_box(c((core::ptr::null_mut(),core::ptr::null_mut())));
 core::hint::black_box(d((core::ptr::null(),1)));core::hint::black_box(e((1,core::ptr::null())));
 core::hint::black_box(f((core::ptr::null_mut(),true)));core::hint::black_box(g((true,core::ptr::null_mut())));
 core::hint::black_box(h((core::ptr::null(),'x')));core::hint::black_box(i((1,core::ptr::null())));
 core::hint::black_box(j((1.,core::ptr::null_mut())));core::hint::black_box(k((core::ptr::null(),1)));
 core::hint::black_box(l((core::ptr::null(),1)));
}
