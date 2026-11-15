// Generic source templates: no enumeration of type/const instantiations.
pub fn identity<T: Copy>(value: T) -> T { value }
pub fn array_identity<T: Copy, const N: usize>(value: [T; N]) -> [T; N] { value }
pub fn concrete(value: [u16; 3]) -> [u16; 3] { value }
// A direct call keeps source MIR and leaves callee resolution to Lean.
pub fn calls(value: u8) -> u8 { identity(value) }

pub struct Link<T> {
    pub value: T,
    pub next: *const Link<T>,
}
pub fn link_identity(value: Link<u8>) -> Link<u8> { value }

pub fn requires_const<const N: usize>(value: u8) -> u8 {
    if false { let _ = const { assert!(N != 0); }; }
    value
}
#[track_caller]
pub fn tracked(value: u8) -> u8 { value }
#[target_feature(enable = "sse2")]
pub unsafe fn feature_identity(value: u8) -> u8 { value }
