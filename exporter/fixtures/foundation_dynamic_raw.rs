pub fn dynamic_input(_value: *const (dyn Fn() -> i32 + Sync + std::panic::RefUnwindSafe)) {}
