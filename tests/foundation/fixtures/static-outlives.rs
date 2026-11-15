pub fn static_identity<T: 'static>(value: T) -> T { value }
pub fn unit() { static_identity(()) }
