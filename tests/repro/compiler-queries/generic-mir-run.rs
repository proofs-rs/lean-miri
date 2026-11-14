#![feature(unboxed_closures, fn_traits)]
#[path = "generic-mir.rs"]
mod generic;
use generic::*;
static VALUE: u32 = 43;
fn main() {
    let a = GenericMirIdentity(7_u8);
    let b = GenericMirPair(9_u64, 11_u64);
    let c = GenericMirArray(13_u64, 17_u64);
    let d = GenericMirConstIdentity::<u64, 3>([19, 23, 29]);
    let e = GenericMirChoice(true, 31_u64, 37_u64);
    let f = GenericMirRustCall((41_u64,));
    assert_eq!(a as u64 + b.0 + b.1 + c[0] + c[1] + d[0] + d[1] + d[2] + e + f.0, 200);
    assert_eq!(GenericMirIdentity(47_u64), 47);
    assert_eq!(*GenericMirIdentity(&VALUE), 43);
    assert_eq!(GenericMirChoice(false, 31_u64, 37_u64), 37);
    // Unsupported raw constructor families remain explicit material bodies.
    let pointer: fn(u8) -> u8 = GenericMirIdentity::<u8>;
    assert_eq!(GenericMirIdentity(pointer)(53), 53);
    let higher_ranked: for<'a> fn(&'a u32) -> &'a u32 = reference_identity;
    assert_eq!(*GenericMirIdentity(higher_ranked)(&VALUE), 43);
}
#[inline(never)] fn reference_identity(value: &u32) -> &u32 { value }
