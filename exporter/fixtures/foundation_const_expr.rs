const SUM: u8 = 18 + 19;
const BRANCH: u8 = if SUM > 10 { SUM - 1 } else { 3 };
const OTHERWISE: u8 = if 1_u8 > 10 { 99 } else { 6 * 7 };
const WIDE: u16 = 300 * 2;
pub fn sum() -> u8 { SUM }
pub fn branch() -> u8 { BRANCH }
pub fn otherwise() -> u8 { OTHERWISE }
pub fn wide() -> u16 { WIDE }
// Retain an ordinary byte argument for the existing bounded fixed-frame runner.
pub fn frame(_: u8) -> u8 { BRANCH }
