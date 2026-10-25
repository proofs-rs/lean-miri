#![no_std]

use ctfe_producer_types::{Opcode, Pair, Token};

/// External tuple-struct constructor: expected to demand InstanceKind::Item
/// MIR from the dependency crate's CTFE MIR table.
pub fn make_pair(left: u16, right: u32) -> Pair {
    let constructor: fn(u16, u32) -> Pair = Pair;
    constructor(left, right)
}

/// External enum-variant constructor: a second generated Ctor definition.
pub fn make_token(value: u32) -> Token {
    let constructor: fn(u32) -> Token = Token::Number;
    constructor(value)
}

/// CTFE initializer whose MIR contains a direct call to an external
/// always-const free function.
pub const FREE_RESULT: u32 = ctfe_producer_types::compile_time_add(35, 7);

/// CTFE initializer whose MIR contains a direct call to an external
/// always-const associated function.
pub const ASSOCIATED_RESULT: u32 = Opcode::compile_time_xor(35, 0x5a);
