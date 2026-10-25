#![no_std]

/// Public root whose argument type contains the unsized `str` pointee.
#[unsafe(no_mangle)]
pub fn str_byte_at(value: &str, index: usize) -> u8 {
    value.as_bytes()[index]
}

#[unsafe(no_mangle)]
pub fn str_length_with_first_byte(value: &str) -> usize {
    value.len() + value.as_bytes()[0] as usize
}
