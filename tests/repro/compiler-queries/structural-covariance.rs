#![no_std]
#![allow(dead_code)]
pub type C0 = bool;
pub type C1 = u8;
pub type C2 = u16;
pub type C3 = *const bool;
pub type C4 = *mut bool;
pub type C5 = *mut u8;
pub type C6 = &'static bool;
pub type C7 = &'static mut bool;
pub type C8 = &'static mut u8;
pub type C9 = [bool; 7];
pub type C10 = [u8; 7];
pub type C11 = [bool];
pub type C12 = [u8];
pub type C13 = (*mut bool, bool);
pub type C14 = (*mut u8, bool);
pub type C15 = (*mut bool,);
pub fn covariance_root() {}
