#![no_std]
#[derive(Clone, Copy)] pub enum DefaultRepr { A, B }
#[derive(Clone, Copy)] #[repr(C)] pub enum CRepr { A, B }
#[derive(Clone, Copy)] #[repr(u8)] pub enum U8Repr { A, B }
#[derive(Clone, Copy)] #[repr(i8)] pub enum I8Repr { A = -1, B = 1 }
#[derive(Clone, Copy)] #[repr(u16)] pub enum U16Repr { A, B }
#[derive(Clone, Copy)] #[repr(i128)] pub enum I128Repr { A = -1, B = 1 }
#[derive(Clone, Copy)] pub struct Plain(pub u32);
pub fn discriminant_types(a: DefaultRepr, b: CRepr, c: U8Repr, d: I8Repr,
    e: U16Repr, f: I128Repr, g: Plain, h: [u8; 3], p: *const Plain) -> u8 {
    let _ = (a,b,c,d,e,f,g,h,p);
    0
}
