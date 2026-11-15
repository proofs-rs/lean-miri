pub fn dynamic_input(_value: &'static (dyn Fn() -> i32 + Sync + std::panic::RefUnwindSafe)) {}
pub fn generic_dynamic_input<T: 'static>(
    _value: &'static (dyn Fn() -> T + Sync + std::panic::RefUnwindSafe),
) {}
pub fn once_input(_value: &'static (dyn FnOnce() -> i32 + Sync + std::panic::RefUnwindSafe)) {}
