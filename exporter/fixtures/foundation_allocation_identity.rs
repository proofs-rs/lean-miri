#![crate_type = "lib"]

pub fn literal() -> &'static [u8; 4] {
    b"same"
}

// A compiler-reference fixture: CTFE/promoted source evaluation is not yet a
// supported foundation allocation constructor. Equal bytes need not share IDs.
pub fn evaluated() -> &'static [u8; 4] {
    &const { [115u8, 97, 109, 101] }
}
