// Retain this const definition's MIR expression; do not export its CTFE answer.
const VALUE: u8 = 37;
pub fn scalar(_argument: u8) -> u8 { VALUE }

const ARITHMETIC: u8 = 18 + 19;
pub fn arithmetic(_argument: u8) -> u8 { ARITHMETIC }
