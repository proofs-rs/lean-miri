pub fn identity<T>(value: T) -> T {
    value
}

pub fn wrap<T: Copy>(value: T) -> T {
    identity(value)
}
