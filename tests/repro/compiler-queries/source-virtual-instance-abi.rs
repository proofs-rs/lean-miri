#![no_std]
#![feature(arbitrary_self_types_pointers, rustc_attrs)]
#![allow(internal_features)]
pub trait Value<T> {
    fn shared(&self, value:T)->T;
    fn mutate(&mut self, value:T)->T;
}
pub trait Raw {
    fn read(self:*const Self, value:u32)->u32;
    fn write(self:*mut Self, value:u64)->u64;
}
pub trait Controls {
    #[rustc_nounwind] fn may_unwind(&self, value:u32)->u32 {value}
    #[track_caller] fn tracked(&self)->u32;
}
pub fn root(a:&dyn Value<u32>, b:&mut dyn Value<u64>, c:&dyn Value<bool>,
    d:&mut (dyn Value<u32>+Unpin), p:*const dyn Raw,q:*mut dyn Raw,r:&dyn Controls){
 core::hint::black_box(a.shared(1));
 core::hint::black_box(b.mutate(2));
 core::hint::black_box(c.shared(true));
 core::hint::black_box(d.mutate(3));
 unsafe {core::hint::black_box(Raw::read(p,4));core::hint::black_box(Raw::write(q,5));}
 core::hint::black_box(r.may_unwind(6));
 core::hint::black_box(r.tracked());
}
