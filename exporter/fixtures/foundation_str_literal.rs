#![crate_type = "lib"]

// UTF-8 byte length is eight, while this text has five Unicode scalar values.
pub fn literal() -> &'static str { "Lean🦀" }
