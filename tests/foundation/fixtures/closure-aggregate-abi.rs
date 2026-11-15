fn main() {}
pub fn local_probe<F: FnOnce() -> isize>(function: F) -> Result<isize, Box<dyn std::any::Any + Send>> {
    Ok(function())
}
