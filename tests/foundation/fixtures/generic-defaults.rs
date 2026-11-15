#![allow(dead_code)]
pub struct Packet<T = u8> { pub field: T }
pub fn identity(value: Packet<u16>) -> Packet<u16> { value }
pub fn default_identity(value: Packet) -> Packet { value }
