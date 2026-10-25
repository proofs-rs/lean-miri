#![allow(clippy::exit)]

// Derived from source125-varying-choice-probe's genuine main input.
// Keep the exponent operand explicit and the base runtime-dependent so that
// a fresh exporter capture can check the exponent-zero intrinsic path.
fn main() {
    let argc = std::env::args_os().count() as f32;
    let value = argc.powi(0);
    std::process::exit(value as i32);
}
