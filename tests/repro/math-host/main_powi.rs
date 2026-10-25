#![allow(clippy::exit)]

fn main() {
    let argc = std::env::args_os().count() as f32;
    let first = argc.powi(2);
    let second = (argc + 1.0).powi(2);
    std::process::exit((first + second) as i32);
}
