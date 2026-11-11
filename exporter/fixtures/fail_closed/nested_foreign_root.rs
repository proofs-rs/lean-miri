#![no_std]

pub fn identity(value: u8) -> u8 {
    // rustc's printed def-path for this foreign block is also `identity`.
    unsafe extern "C" {
        fn external_symbol();
    }
    value
}
