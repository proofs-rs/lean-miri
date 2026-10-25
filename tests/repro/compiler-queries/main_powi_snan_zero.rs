#![allow(clippy::exit)]

// Focused source candidate for the signaling-NaN exponent-zero policy. A fresh
// rustc exporter capture must confirm that it retains powif32 in MIR before
// this can serve as a runtime fixture.
fn main() {
    let argc = std::env::args_os().count() as u32;
    let payload = (argc & 0x003f_ffff) | 1;
    let signaling = f32::from_bits(0x7f80_0000 | payload);
    let value = signaling.powi(0);
    std::process::exit(value.is_nan() as i32);
}
