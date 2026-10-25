#![no_std]
// Build as an rlib before exporting metadata-consumer.rs. CTFE creates this
// symbolic vtable in the producer; the consumer imports its encoded allocation.
pub trait Marker<'a>: Sync { fn value(&self, input: &'a u8) -> u8; }
pub struct Value;
impl<'a> Marker<'a> for Value { fn value(&self, input: &'a u8) -> u8 { *input } }
pub const OBJECT: &(dyn for<'named> Marker<'named> + Sync) = &Value;
