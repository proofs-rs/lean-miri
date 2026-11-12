#![no_std]
#![allow(dead_code)]
pub struct Co<T>(pub *const T);
pub struct Contra<T>(pub fn(T));
pub struct Inv<T>(pub *mut T);
pub struct Cell<T>(pub core::cell::UnsafeCell<T>);
pub struct Nested<T>(pub Co<Contra<T>>);
pub struct Rec<T>(pub T,pub *const Rec<T>);
pub type N0=Co<u8>;
pub type N1=Co<u16>;
pub type N2=Contra<u8>;
pub type N3=Contra<u16>;
pub type N4=Inv<u8>;
pub type N5=Inv<u16>;
pub type N6=Cell<u8>;
pub type N7=Cell<u16>;
pub type N8=Nested<u8>;
pub type N9=Nested<u16>;
pub type N10=Rec<u8>;
pub type N11=Rec<u16>;
pub type N12=*mut Co<u8>;
pub type N13=*mut Co<u16>;
pub type N14=(Co<u8>,Contra<u8>);
pub type N15=(Co<u16>,Contra<u8>);
#[inline(never)]
pub unsafe fn transfer(value: Co<u8>) -> Co<u16> { unsafe { core::mem::transmute(value) } }
pub fn nominal_covariance_root(_n0: N0,_n1: N1,_n2: N2,_n3: N3,_n4: N4,_n5: N5,_n6: N6,_n7: N7,_n8: N8,_n9: N9,_n10: N10,_n11: N11,_n12: N12,_n13: N13,_n14: N14,_n15: N15) { let _ = unsafe { transfer(_n0) }; }
