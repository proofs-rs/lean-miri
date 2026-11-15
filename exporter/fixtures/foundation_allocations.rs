#![crate_type = "lib"]

pub fn literal() -> &'static str {
    "foundation-bytes"
}

pub fn bytes() -> &'static [u8; 4] {
    b"Miri"
}
