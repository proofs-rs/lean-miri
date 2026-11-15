pub fn invoke<F: FnOnce() -> T, T>(function: F) -> T {
    function()
}
