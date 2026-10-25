#![feature(repr_simd)]
#[repr(C)]
pub union U { pub a: u32, pub b: f64 }
pub enum E { A(u32), B(u64) }
#[repr(simd)]
pub struct V(pub [u32; 4]);
pub fn records(e: E, u: U, p: &u32, a: [u16; 3], f: f64, v: V, n: Option<&u32>) {
    let _ = (e, u, p, a, f, v, n);
}
